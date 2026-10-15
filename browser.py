#!/usr/bin/env python3
"""Foundation package browser.

Easiest: put this file in the folder with game.package and double-click it (or run: python browser.py).
Or:  python3 browser.py game.package [engine.package loading.package ...] [--port 8765] [--no-browser]

Reads the .package files directly (nothing is unpacked or modified) and serves a
browsing page on http://localhost:8765 that you open in your normal web browser.
Stop it with Ctrl+C.
"""
import io, os, sys, json, struct, uuid, mimetypes, argparse, threading, time, webbrowser
from collections import OrderedDict
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler
from urllib.parse import urlparse, parse_qs

ZERO_GUID = '00000000-0000-0000-0000-000000000000'


class FormatError(Exception):
    pass


# ---------------------------------------------------------------- prefab / .data / .meta containers
def looks_like_container(head, size):
    if len(head) < 16:
        return False
    ver, z, plen, _ = struct.unpack_from('<IIII', head, 0)
    return ver == 2 and z == 0 and plen == size - 12


# Value kinds. 0, 2, 4, 6, 7 and 8 were seen directly, and so was 1 (8 bytes). 3 and 5 are guesses from the
# pattern uint32/uint64/int32/int64/float32/float64 and have not been seen in a file yet.
KINDS = {0: ('uint', '<I', 4), 1: ('uint64', '<Q', 8), 2: ('int', '<i', 4), 3: ('int64', '<q', 8),
         4: ('float', '<f', 4), 5: ('double', '<d', 8)}


class Container:
    """A node tree stored as a linked structure. Node (16 bytes): name_idx, next_sibling,
    first_child, first_value (offsets are relative to the data section, 0 = none).
    Value record: tag_idx, next_record, kind, payload. A node's value is a linked list of
    such records (e.g. a colour's r/g/b/a, or a .meta file's id + type)."""

    def __init__(self, d):
        if not looks_like_container(d[:16], len(d)):
            raise FormatError("not a prefab/data/meta container")
        n = struct.unpack_from('<I', d, 12)[0]
        pos, strs = 16, []
        try:
            for _ in range(n):
                e = d.index(b'\0', pos)
                strs.append(d[pos:e].decode('utf-8', 'replace'))
                pos = e + 1
            dlen = struct.unpack_from('<I', d, pos)[0]
        except (ValueError, struct.error):
            raise FormatError("bad string table")
        self.d, self.strs, self.base = d, strs, pos + 4
        if dlen != len(d) - self.base or dlen < 20:
            raise FormatError("data length mismatch")
        self.dlen = dlen

    def u(self, o):
        if o < 0 or o + 4 > self.dlen:
            raise FormatError("offset outside data")
        return struct.unpack_from('<I', self.d, self.base + o)[0]

    def fields(self, v):
        out = []
        while v:
            if len(out) > 256 or v + 12 > self.dlen:
                raise FormatError("bad value record")
            tag, nxt, kind = self.u(v), self.u(v + 4), self.u(v + 8)
            if tag >= len(self.strs):
                raise FormatError("bad name index")
            p = self.base + v + 12
            name = self.strs[tag]
            try:
                if kind == 7:
                    e = self.d.index(b'\0', p)
                    typ, val = ('class' if name == 'type' else 'string'), self.d[p:e].decode('utf-8', 'replace')
                elif kind == 17:  # UTF-16LE text, ends with a 16-bit NUL
                    e = p
                    while True:
                        e = self.d.index(b'\0\0', e)
                        if (e - p) % 2 == 0:
                            break
                        e += 1
                    typ, val = 'string', self.d[p:e].decode('utf-16-le', 'replace')
                elif kind == 16:  # blob: u32 byte length, 4 bytes (always 0 so far), raw bytes (float32 lists seen)
                    n = struct.unpack_from('<I', self.d, p)[0]
                    if p + 8 + n > len(self.d):
                        raise FormatError("blob runs past end of file")
                    raw = self.d[p + 8:p + 8 + n]
                    if n % 4 == 0 and n:
                        fl = struct.unpack('<%df' % min(n // 4, 24), raw[:96])
                        txt = ', '.join('%.6g' % x for x in fl) + (', …' if n // 4 > 24 else '')
                    else:
                        txt = raw[:32].hex(' ')
                    typ, val = 'blob', '%d bytes: [%s]' % (n, txt)
                elif kind == 6:
                    typ, val = 'bool', bool(struct.unpack_from('<I', self.d, p)[0])
                elif kind == 8:
                    typ, val = 'guid', str(uuid.UUID(bytes=self.d[p:p + 16]))
                elif kind in KINDS:
                    typ, fmt, _ = KINDS[kind]
                    val = struct.unpack_from(fmt, self.d, p)[0]
                    if isinstance(val, float):
                        if val != val or abs(val) == float('inf'):
                            val = str(val)
                        elif kind == 4:
                            val = float('%.7g' % val)  # drop float32 -> float64 noise (1.4939999 -> 1.494)
                else:
                    raise FormatError("unknown value kind %d" % kind)
            except (ValueError, struct.error):
                raise FormatError("value runs past end of file")
            out.append({'tag': name, 'type': typ, 'value': val})
            v = nxt
        return out

    def node(self, o):
        if o < 4 or o + 16 > self.dlen:
            raise FormatError("bad node offset")
        nm, nxt, ch, val = self.u(o), self.u(o + 4), self.u(o + 8), self.u(o + 12)
        if nm >= len(self.strs):
            raise FormatError("bad name index")
        return {'name': self.strs[nm], 'off': o, 'next': nxt, 'child': ch, 'fields': self.fields(val)}

    def page(self, o, skip=0, limit=200):
        """Siblings starting at node offset o: (items, next_skip or None)."""
        items, i, guard = [], 0, self.dlen // 16 + 2
        while o:
            if i > guard:
                raise FormatError("sibling loop")
            if i >= skip:
                nd = self.node(o)
                items.append(nd)
                o = nd['next']
                i += 1
                if len(items) >= limit:
                    return items, (i if o else None)
            else:
                if o < 4 or o + 16 > self.dlen:
                    raise FormatError("bad node offset")
                o = self.u(o + 4)
                i += 1
        return items, None

    def root_guid(self):
        """For .meta files: (id, type) of the root node."""
        nd = self.node(4)
        f = {x['tag']: x['value'] for x in nd['fields']}
        return f.get('id'), f.get('type')


def fmt_value(v):
    return ('%.6g' % v) if isinstance(v, float) else str(v)


def fmt_fields(fields):
    if not fields:
        return ''
    if len(fields) == 1:
        return ' = %s  (%s)' % (fmt_value(fields[0]['value']), fields[0]['type'])
    return ' = {%s}  (%s)' % (', '.join('%s=%s' % (f['tag'], fmt_value(f['value'])) for f in fields),
                              ', '.join(dict.fromkeys(f['type'] for f in fields)))


# ---------------------------------------------------------------- .package reader
class Dir:
    __slots__ = ('kids', 'exts')
    def __init__(self): self.kids, self.exts = {}, None


class File:
    __slots__ = ('off', 'len')
    def __init__(self, off, ln): self.off, self.len = off, ln


class Package:
    """Layout (little-endian): u32 version, 32-byte ascii id, u32 data_offset,
    u32 total_files, u32 top_count, then entries:
      u32 name_len, name, u8 is_dir;  dir: u32 count, u32 skip, children;
      file: u64 offset (from data_offset), u64 length."""

    def __init__(self, path):
        self.path = path
        self.name = os.path.splitext(os.path.basename(path))[0]
        self.size = os.path.getsize(path)
        with open(path, 'rb') as f:
            head = f.read(48)
            if len(head) < 48:
                raise FormatError("file too small")
            self.version = struct.unpack_from('<I', head, 0)[0]
            self.id = head[4:36].decode('ascii', 'replace')
            self.data_off, self.total, count = struct.unpack_from('<III', head, 36)
            if not 48 < self.data_off <= self.size:
                raise FormatError("header does not look like a Foundation package")
            f.seek(0)
            idx = io.BytesIO(f.read(self.data_off))
        idx.seek(48)
        self.root = Dir()
        self.files = []  # (path, File)
        self._read_dir(idx, self.root, count, '', 0)
        self.lower = [(p.lower(), p) for p, _ in self.files]

    def _read_dir(self, b, d, n, prefix, depth):
        if depth > 64:
            raise FormatError("directories nested too deeply")
        for _ in range(n):
            raw = b.read(4)
            if len(raw) < 4:
                raise FormatError("index truncated")
            nl = struct.unpack('<I', raw)[0]
            if not 0 < nl <= 4096:
                raise FormatError("bad name length (layout differs?)")
            name = b.read(nl).decode('utf-8', 'replace')
            flag = b.read(1)
            if len(flag) < 1:
                raise FormatError("index truncated")
            if flag[0]:
                cnt, _skip = struct.unpack('<II', b.read(8))
                sub = Dir()
                d.kids[name] = sub
                self._read_dir(b, sub, cnt, prefix + name + '/', depth + 1)
            else:
                off, ln = struct.unpack('<QQ', b.read(16))
                if self.data_off + off + ln > self.size:
                    raise FormatError("file data outside the package")
                fl = File(off, ln)
                d.kids[name] = fl
                self.files.append((prefix + name, fl))

    def find(self, path):
        node = self.root
        for part in [p for p in path.split('/') if p]:
            if not isinstance(node, Dir) or part not in node.kids:
                return None
            node = node.kids[part]
        return node

    def read(self, fl, start=0, length=None):
        if length is None or start + length > fl.len:
            length = max(0, fl.len - start)
        with open(self.path, 'rb') as f:
            f.seek(self.data_off + fl.off + start)
            return f.read(length)


PACKS = {}


EXT_ALIAS = {'tiff': 'tif', 'jpeg': 'jpg'}  # shown and filtered as one type


def file_ext(name):
    e = name.rsplit('.', 1)[-1].lower() if '.' in name.strip('.') else '(none)'
    return EXT_ALIAS.get(e, e)


def dir_exts(d):
    """Set of file extensions anywhere below folder d (cached on the folder)."""
    if d.exts is None:
        out = set()
        for k, v in d.kids.items():
            out |= dir_exts(v) if isinstance(v, Dir) else {file_ext(k)}
        d.exts = out
    return d.exts


def want_exts(q):
    return {e.strip().lower() for e in q.get('ext', '').split(',') if e.strip()}


# ---------------------------------------------------------------- GUID index (from .meta files)
class GuidIndex:
    """Every asset has a sibling '<asset>.meta' holding its GUID and class. Model files also list a GUID
    for each node/mesh inside them. Built in the background."""

    def __init__(self):
        self.map = {}  # guid -> (pkg name, asset path, label, is_sub_asset)
        self.total = self.done = self.bad = 0
        self.finished = False

    @staticmethod
    def is_meta(path, fl):
        """Real .meta files are small. Names like Model.fbx.data-xbin.meta are bulk data (megabytes)
        that merely end in .meta, so they are skipped here."""
        return path.endswith('.meta') and not path.endswith('.data-xbin.meta') and fl.len <= 1024 * 1024

    def add_meta(self, c, pkg_name, asset_path):
        stack = [4]
        while stack:
            nd = c.node(stack.pop())
            if nd['next']:
                stack.append(nd['next'])
            if nd['name'] != 'meta':
                continue  # settings subtrees (importer etc.) hold no asset ids
            f = {x['tag']: x['value'] for x in nd['fields']}
            gid = f.get('id')
            if gid and gid != ZERO_GUID and gid not in self.map:
                is_sub = nd['off'] != 4
                self.map[gid] = (pkg_name, asset_path, f.get('type') or f.get('name'), is_sub, f.get('name'))
            if nd['child']:
                stack.append(nd['child'])

    def build(self, packs):
        try:
            for p in packs:
                self.total += sum(1 for path, fl in p.files if self.is_meta(path, fl))
            for p in packs:
                metas = sorted(((path, fl) for path, fl in p.files if self.is_meta(path, fl)), key=lambda x: x[1].off)
                with open(p.path, 'rb') as f:
                    for path, fl in metas:
                        self.done += 1
                        f.seek(p.data_off + fl.off)
                        data = f.read(fl.len)
                        try:
                            self.add_meta(Container(data), p.name, path[:-5])
                        except (FormatError, struct.error, KeyError, RecursionError):
                            self.bad += 1
        finally:
            self.finished = True
        REFS.build(packs)

    def lookup(self, gid):
        hit = self.map.get(gid)
        if not hit:
            return None
        pkg = PACKS.get(hit[0])
        if pkg is None or not isinstance(pkg.find(hit[1]), File):
            return None
        return {'pkg': hit[0], 'path': hit[1], 'type': hit[2], 'sub': hit[3], 'name': hit[4] if len(hit) > 4 else None}


GUIDS = GuidIndex()


# ---------------------------------------------------------------- Who links to whom
# Every GUID-valued field in a container is stored as  u32 kind=8  followed by 16 bytes, so a file's
# outgoing links can be found with a byte scan, and "used by" is the same scan run over every file once.
import re, bisect
_GUID_RE = re.compile(rb'(?=\x08\x00\x00\x00(.{16}))', re.S)
_NOSCAN = {'png', 'jpg', 'jpeg', 'gif', 'tga', 'tif', 'tiff', 'dds', 'webm', 'ttf', 'otf', 'fbx', 'wav', 'ogg', 'mp3', 'txt', 'json'}
_ZERO16 = b'\0' * 16


def scan_guids(data):
    """{guid bytes: count} for a container's data, {} if it is not a container."""
    if not looks_like_container(data[:16], len(data)):
        return {}
    out = {}
    for m in _GUID_RE.finditer(data):
        g = m.group(1)
        if g != _ZERO16:
            out[g] = out.get(g, 0) + 1
    return out


class RefIndex:
    """For every container file, the set of GUIDs it mentions. Built in the background once the
    GUID index is done; asking 'which files mention these GUIDs' is then a byte search."""

    def __init__(self):
        self.blob = bytearray()
        self.starts = []
        self.owners = []
        self.total = self.done = 0
        self.finished = False
        self._by_file = None
        self.texmap = {}  # texture file name (lower case) -> [(pkg, model path)]

    @staticmethod
    def wanted(path, fl):
        return fl.len <= 4 * 1024 * 1024 and fl.len >= 16 and ext_of(path) not in _NOSCAN and not path.endswith('.data-xbin.meta')

    def build(self, packs):
        try:
            for p in packs:
                self.total += sum(1 for path, fl in p.files if self.wanted(path, fl))
            for p in packs:
                for path, fl in p.files:
                    if ext_of(path) == 'fbx' and 24 < fl.len < 8 * 1024 * 1024:
                        try:
                            for mt in parse_model_desc(p.read(fl))[1]:
                                t = mt.get('tex')
                                if t and t != '.':
                                    lst = self.texmap.setdefault(t.lower(), [])
                                    if (p.name, path) not in lst:
                                        lst.append((p.name, path))
                        except (FormatError, struct.error, IndexError, RecursionError):
                            pass
            for p in packs:
                files = sorted(((path, fl) for path, fl in p.files if self.wanted(path, fl)), key=lambda x: x[1].off)
                with open(p.path, 'rb') as f:
                    for path, fl in files:
                        self.done += 1
                        f.seek(p.data_off + fl.off)
                        try:
                            gs = scan_guids(f.read(fl.len))
                        except (struct.error, MemoryError):
                            continue
                        if gs:
                            self.starts.append(len(self.blob))
                            self.owners.append((p.name, path))
                            self.blob += b''.join(gs)
        finally:
            self.finished = True

    def by_file(self):
        if self._by_file is None:
            d = {}
            for g, hit in list(GUIDS.map.items()):
                d.setdefault((hit[0], hit[1]), []).append(g)
            self._by_file = d
        return self._by_file

    def who_mentions(self, guid_bytes):
        owners, blob = set(), self.blob
        pos = blob.find(guid_bytes)
        while pos >= 0:
            if pos % 16 == 0:
                owners.add(bisect.bisect_right(self.starts, pos) - 1)
            pos = blob.find(guid_bytes, pos + 1)
        return owners


REFS = RefIndex()


def _norm_owner(pkg, path):
    """A file's links often sit in its sibling '.meta'; report the asset itself when it exists."""
    if path.endswith('.meta') and isinstance(pkg.find(path[:-5]), File):
        return path[:-5]
    return path


def links_uses(pkg, path):
    """Files this file points to: [{pkg, path, count, via, subs}], unresolved link count."""
    rows, unresolved = {}, 0
    for suffix in ('', '.meta', '.prefab.meta'):
        n = pkg.find(path + suffix)
        if not isinstance(n, File) or n.len > 16 * 1024 * 1024:
            continue
        try:
            gs = scan_guids(pkg.read(n))
        except (struct.error, MemoryError):
            continue
        for g, cnt in gs.items():
            gid = str(uuid.UUID(bytes=g))
            hit = GUIDS.lookup(gid)
            if hit is None:
                unresolved += cnt
                continue
            tp = hit['path']
            if hit['pkg'] == pkg.name and (tp == path or tp.startswith(path + '.')):
                continue  # its own parts / siblings
            k = (hit['pkg'], tp)
            r = rows.setdefault(k, {'pkg': hit['pkg'], 'path': tp, 'count': 0, 'via': [], 'subs': [], 'type': hit.get('type')})
            r['count'] += cnt
            if (suffix or 'file') not in r['via']:
                r['via'].append(suffix or 'file')
            if hit['sub'] and hit.get('name') and hit['name'] not in r['subs'] and len(r['subs']) < 6:
                r['subs'].append(hit['name'])
            if hit['sub'] and 'focus' not in r:
                r['focus'] = gid if len(r['subs']) == 1 else None
    node = pkg.find(path)
    if ext_of(path) == 'fbx' and isinstance(node, File) and node.len < 8 * 1024 * 1024:
        try:
            for mt in parse_model_desc(pkg.read(node))[1]:
                t = mt.get('tex')
                hit = find_texture(pkg, path, t) if t and t != '.' else None
                if hit:
                    r = rows.setdefault(hit, {'pkg': hit[0], 'path': hit[1], 'count': 0, 'via': [], 'subs': [], 'type': None})
                    r['count'] += 1
                    if 'material table' not in r['via']:
                        r['via'].append('material table')
        except (FormatError, struct.error, IndexError, RecursionError):
            pass
    return sorted(rows.values(), key=lambda r: (-r['count'], r['path'])), unresolved


def links_reach(pkg, path, max_files=300, max_depth=8):
    """Models reachable by following 'uses' links from a file: [{pkg, path, focus, chain}]."""
    out, seen = [], {(pkg.name, path)}
    queue = [((pkg.name, path), None, [path.rsplit('/', 1)[-1]])]
    n = 0
    while queue and n < max_files:
        (kp, kpath), _, chain = queue.pop(0)
        p = PACKS.get(kp)
        if p is None or len(chain) > max_depth:
            continue
        n += 1
        rows, _u = links_uses(p, kpath)
        for r in rows:
            k = (r['pkg'], r['path'])
            if k in seen:
                continue
            seen.add(k)
            ch = chain + [r['path'].rsplit('/', 1)[-1]]
            ext = ext_of(r['path'])
            if ext == 'fbx':
                out.append({'pkg': r['pkg'], 'path': r['path'], 'focus': r.get('focus'), 'chain': ch, 'sub': (r['subs'] or [None])[0]})
            elif ext not in ('png', 'jpg', 'tga', 'tif', 'tiff', 'dds'):
                queue.append((k, None, ch))
    return out


def links_used_by(pkg, path):
    mine = REFS.by_file().get((pkg.name, path), [])
    rows = {}
    for gid in mine:
        gb = uuid.UUID(gid).bytes
        for oi in REFS.who_mentions(gb):
            opkg, opath = REFS.owners[oi]
            op = PACKS.get(opkg)
            if op is None:
                continue
            opath = _norm_owner(op, opath)
            if opkg == pkg.name and (opath == path or opath.startswith(path + '.')):
                continue
            r = rows.setdefault((opkg, opath), {'pkg': opkg, 'path': opath, 'subs': []})
            hit = GUIDS.map.get(gid)
            if hit and hit[3] and hit[4] and hit[4] not in r['subs'] and len(r['subs']) < 6:
                r['subs'].append(hit[4])
    for opkg, opath in REFS.texmap.get(path.rsplit('/', 1)[-1].lower(), ()):
        op = PACKS.get(opkg)
        if op is not None and find_texture(op, opath, path.rsplit('/', 1)[-1]) == (pkg.name, path):
            rows.setdefault((opkg, opath), {'pkg': opkg, 'path': opath, 'subs': ['material table']})
    return sorted(rows.values(), key=lambda r: r['path'])

# Parsed containers are cached so expanding a big file does not re-read it each time.
_cache = OrderedDict()
_cache_lock = threading.Lock()


def get_container(pkg, path, node):
    key = (pkg.name, path)
    with _cache_lock:
        if key in _cache:
            _cache.move_to_end(key)
            return _cache[key]
    if node.len > 256 * 1024 * 1024:
        raise FormatError("file too large to decode")
    c = Container(pkg.read(node))
    with _cache_lock:
        _cache[key] = c
        while len(_cache) > 3:
            _cache.popitem(last=False)
    return c


# ---------------------------------------------------------------- image conversion (TGA / TIFF / DDS -> PNG)
# Browsers cannot show these formats, so the server decodes them to RGBA and re-encodes as PNG.
# Decoders are written with the standard library only. Anything they do not understand
# (BC7, tiled or JPEG TIFFs, ...) is handed to Pillow if it happens to be installed.
import zlib


class ImgError(Exception):
    pass


def png_encode(w, h, rgba):
    """rgba: bytes/bytearray of w*h*4 -> PNG file bytes (RGB when fully opaque)."""
    if w < 1 or h < 1 or len(rgba) < w * h * 4:
        raise ImgError('empty image')
    opaque = rgba[3::4].count(255) == w * h if w * h else True
    raw = bytearray()
    if opaque:
        ctype, step = 2, 3
        rgb = bytearray(w * h * 3)
        rgb[0::3], rgb[1::3], rgb[2::3] = rgba[0::4], rgba[1::4], rgba[2::4]
        src = rgb
    else:
        ctype, step, src = 6, 4, rgba
    rowb = w * step
    for y in range(h):
        raw.append(0)
        raw += src[y * rowb:(y + 1) * rowb]

    def chunk(t, d):
        c = struct.pack('>I', len(d)) + t + d
        return c + struct.pack('>I', zlib.crc32(t + d) & 0xffffffff)
    return (b'\x89PNG\r\n\x1a\n' + chunk(b'IHDR', struct.pack('>IIBBBBB', w, h, 8, ctype, 0, 0, 0)) +
            chunk(b'IDAT', zlib.compress(bytes(raw), 6)) + chunk(b'IEND', b''))


def _check_dims(w, h):
    if not (0 < w <= 16384 and 0 < h <= 16384) or w * h > 64 * 1024 * 1024:
        raise ImgError('image dimensions are unreasonable (%d x %d)' % (w, h))


# ---- TGA
def decode_tga(d):
    if len(d) < 18:
        raise ImgError('TGA too small')
    idlen, cmt, typ = d[0], d[1], d[2]
    cfirst, clen, csize = struct.unpack_from('<HHB', d, 3)
    w, h, bpp, desc = struct.unpack_from('<HHBB', d, 12)
    _check_dims(w, h)
    if typ not in (1, 2, 3, 9, 10, 11):
        raise ImgError('unsupported TGA type %d' % typ)
    p = 18 + idlen
    pal = None
    if cmt:
        eb = (csize + 7) // 8
        pal = []
        for i in range(clen):
            e = d[p + i * eb:p + i * eb + eb]
            pal.append(_tga_px(e, csize))
        p += clen * eb
    bpx = (bpp + 7) // 8
    need = w * h * bpx
    rle = typ >= 9
    if rle:
        buf = bytearray()
        while len(buf) < need and p < len(d):
            c = d[p]
            p += 1
            n = (c & 127) + 1
            if c & 128:
                buf += d[p:p + bpx] * n
                p += bpx
            else:
                buf += d[p:p + n * bpx]
                p += n * bpx
        buf = bytes(buf[:need])
    else:
        buf = d[p:p + need]
    if len(buf) < need:
        raise ImgError('TGA pixel data truncated')
    out = bytearray(w * h * 4)
    if typ in (1, 9):
        if pal is None:
            raise ImgError('TGA palette missing')
        for i in range(w * h):
            idx = buf[i] - cfirst
            out[i * 4:i * 4 + 4] = pal[idx] if 0 <= idx < len(pal) else b'\0\0\0\xff'
    elif typ in (3, 11):
        if bpp != 8:
            raise ImgError('unsupported grey TGA depth')
        out[0::4] = out[1::4] = out[2::4] = buf
        out[3::4] = b'\xff' * (w * h)
    elif bpp == 24:
        out[0::4], out[1::4], out[2::4] = buf[2::3], buf[1::3], buf[0::3]
        out[3::4] = b'\xff' * (w * h)
    elif bpp == 32:
        out[0::4], out[1::4], out[2::4], out[3::4] = buf[2::4], buf[1::4], buf[0::4], buf[3::4]
        if (desc & 15) == 0:
            out[3::4] = b'\xff' * (w * h)
    elif bpp in (15, 16):
        for i in range(w * h):
            out[i * 4:i * 4 + 4] = _tga_px(buf[i * 2:i * 2 + 2], 16)
    else:
        raise ImgError('unsupported TGA depth %d' % bpp)
    if not desc & 0x20:  # stored bottom-up
        rows = [out[y * w * 4:(y + 1) * w * 4] for y in range(h)]
        out = bytearray().join(reversed(rows))
    if desc & 0x10:  # stored right-to-left
        rows = []
        for y in range(h):
            r = out[y * w * 4:(y + 1) * w * 4]
            px = [r[i:i + 4] for i in range(0, len(r), 4)]
            rows.append(b''.join(reversed(px)))
        out = bytearray().join(rows)
    return w, h, out


def _tga_px(e, size):
    if size in (15, 16):
        v = e[0] | (e[1] << 8)
        r, g, b = (v >> 10) & 31, (v >> 5) & 31, v & 31
        return bytes((r * 255 // 31, g * 255 // 31, b * 255 // 31, 255))
    if size == 24:
        return bytes((e[2], e[1], e[0], 255))
    if size == 32:
        return bytes((e[2], e[1], e[0], e[3]))
    return bytes((e[0], e[0], e[0], 255))


# ---- DDS
def _rgb565(v):
    r, g, b = (v >> 11) & 31, (v >> 5) & 63, v & 31
    return ((r << 3) | (r >> 2), (g << 2) | (g >> 4), (b << 3) | (b >> 2))


def _dxt_color_table(c0, c1, four):
    a, b = _rgb565(c0), _rgb565(c1)
    if four:
        return [a + (255,), b + (255,),
                tuple((2 * a[i] + b[i]) // 3 for i in range(3)) + (255,),
                tuple((a[i] + 2 * b[i]) // 3 for i in range(3)) + (255,)]
    return [a + (255,), b + (255,), tuple((a[i] + b[i]) // 2 for i in range(3)) + (255,), (0, 0, 0, 0)]


def _bc4_table(a0, a1):
    if a0 > a1:
        return [a0, a1] + [((7 - i) * a0 + i * a1) // 7 for i in range(1, 7)]
    return [a0, a1] + [((5 - i) * a0 + i * a1) // 5 for i in range(1, 5)] + [0, 255]


def decode_dds_blocks(fmt, w, h, data):
    bw, bh = (w + 3) // 4, (h + 3) // 4
    size = 8 if fmt in ('BC1', 'BC4') else 16
    if len(data) < bw * bh * size:
        raise ImgError('DDS data truncated')
    out = bytearray(w * h * 4)
    p = 0
    for by in range(bh):
        for bx in range(bw):
            blk = data[p:p + size]
            p += size
            px = [None] * 16
            if fmt in ('BC1', 'BC2', 'BC3'):
                cb = blk[-8:]
                c0, c1, bits = struct.unpack_from('<HHI', cb, 0)
                tab = _dxt_color_table(c0, c1, fmt != 'BC1' or c0 > c1)
                al = None
                if fmt == 'BC2':
                    v = int.from_bytes(blk[:8], 'little')
                    al = [((v >> (4 * i)) & 15) * 17 for i in range(16)]
                elif fmt == 'BC3':
                    t = _bc4_table(blk[0], blk[1])
                    v = int.from_bytes(blk[2:8], 'little')
                    al = [t[(v >> (3 * i)) & 7] for i in range(16)]
                for i in range(16):
                    c = tab[(bits >> (2 * i)) & 3]
                    px[i] = (c[0], c[1], c[2], al[i] if al else c[3])
            else:  # BC4 (one channel) / BC5 (two channels)
                def chan(b):
                    t = _bc4_table(b[0], b[1])
                    v = int.from_bytes(b[2:8], 'little')
                    return [t[(v >> (3 * i)) & 7] for i in range(16)]
                r = chan(blk[:8])
                if fmt == 'BC4':
                    for i in range(16):
                        px[i] = (r[i], r[i], r[i], 255)
                else:
                    g = chan(blk[8:16])
                    for i in range(16):
                        x, y = r[i] / 127.5 - 1, g[i] / 127.5 - 1
                        z = max(0.0, 1 - x * x - y * y) ** 0.5
                        px[i] = (r[i], g[i], int((z + 1) * 127.5), 255)
            for j in range(4):
                y = by * 4 + j
                if y >= h:
                    break
                for i in range(4):
                    x = bx * 4 + i
                    if x < w:
                        o = (y * w + x) * 4
                        out[o:o + 4] = bytes(px[j * 4 + i])
    return out


def decode_dds(d):
    if len(d) < 128 or d[:4] != b'DDS ':
        raise ImgError('not a DDS file')
    h, w = struct.unpack_from('<II', d, 12)
    _check_dims(w, h)
    pf_flags, fourcc, bits, rm, gm, bm, am = struct.unpack_from('<I4sIIIII', d, 80)
    p = 128
    fmt = None
    if pf_flags & 4:  # FOURCC
        if fourcc == b'DX10':
            dxgi, = struct.unpack_from('<I', d, 128)
            p = 148
            fmt = {70: 'BC1', 71: 'BC1', 72: 'BC1', 73: 'BC2', 74: 'BC2', 75: 'BC2', 76: 'BC3', 77: 'BC3', 78: 'BC3',
                   79: 'BC4', 80: 'BC4', 81: 'BC4', 82: 'BC5', 83: 'BC5', 84: 'BC5'}.get(dxgi)
            if dxgi in (28, 29):
                return w, h, _dds_raw(d[p:], w, h, 32, 0xff, 0xff00, 0xff0000, 0xff000000)
            if dxgi in (87, 91):
                return w, h, _dds_raw(d[p:], w, h, 32, 0xff0000, 0xff00, 0xff, 0xff000000)
            if fmt is None:
                raise ImgError('DDS format %d (DXGI) not supported by the built-in decoder' % dxgi)
        else:
            fmt = {b'DXT1': 'BC1', b'DXT2': 'BC2', b'DXT3': 'BC2', b'DXT4': 'BC3', b'DXT5': 'BC3',
                   b'ATI1': 'BC4', b'BC4U': 'BC4', b'ATI2': 'BC5', b'BC5U': 'BC5'}.get(fourcc)
            if fmt is None:
                raise ImgError('DDS format %r not supported by the built-in decoder' % fourcc)
        return w, h, decode_dds_blocks(fmt, w, h, d[p:])
    if pf_flags & 0x40 or pf_flags & 0x20000 or pf_flags & 2:  # RGB / luminance / alpha-only
        return w, h, _dds_raw(d[p:], w, h, bits, rm, gm, bm, am if pf_flags & 1 else 0)
    raise ImgError('DDS pixel format not supported')


def _dds_raw(data, w, h, bits, rm, gm, bm, am):
    bpx = bits // 8
    if bpx not in (1, 2, 3, 4) or len(data) < w * h * bpx:
        raise ImgError('DDS raw data not understood')
    out = bytearray(w * h * 4)

    def ext(v, m):
        if not m:
            return None
        s = (m & -m).bit_length() - 1
        n = (m >> s).bit_length()
        x = (v & m) >> s
        return x * 255 // ((1 << n) - 1)
    for i in range(w * h):
        v = int.from_bytes(data[i * bpx:(i + 1) * bpx], 'little')
        r, g, b = ext(v, rm), ext(v, gm), ext(v, bm)
        if g is None and b is None:
            g = b = r
        a = ext(v, am)
        out[i * 4:i * 4 + 4] = bytes((r or 0, g or 0, b or 0, 255 if a is None else a))
    return out


# ---- TIFF (baseline: strips, none / LZW / PackBits / Deflate, 8-bit or 16-bit samples)
def _lzw_tiff(data, expect):
    out = bytearray()
    table = [bytes((i,)) for i in range(256)] + [b'', b'']
    bitpos, nbits, prev = 0, 9, None
    total = len(data) * 8
    while bitpos + nbits <= total and len(out) < expect:
        v = int.from_bytes(data[bitpos >> 3:(bitpos >> 3) + 4], 'big')
        code = (v >> (32 - (bitpos & 7) - nbits)) & ((1 << nbits) - 1)
        bitpos += nbits
        if code == 257:
            break
        if code == 256:
            table = table[:258]
            nbits, prev = 9, None
            continue
        if prev is None:
            if code >= len(table):
                raise ImgError('bad LZW stream')
            ent = table[code]
        else:
            if code < len(table):
                ent = table[code]
                table.append(table[prev] + ent[:1])
            elif code == len(table):
                ent = table[prev] + table[prev][:1]
                table.append(ent)
            else:
                raise ImgError('bad LZW stream')
        out += ent
        prev = code
        n = len(table)
        nbits = 9 if n < 511 else 10 if n < 1023 else 11 if n < 2047 else 12
    return bytes(out)


def _packbits(data, expect):
    out, p = bytearray(), 0
    while p < len(data) and len(out) < expect:
        n = data[p]
        p += 1
        if n < 128:
            out += data[p:p + n + 1]
            p += n + 1
        elif n > 128:
            out += data[p:p + 1] * (257 - n)
            p += 1
    return bytes(out)


def decode_tiff(d):
    if len(d) < 8 or d[:2] not in (b'II', b'MM'):
        raise ImgError('not a TIFF file')
    e = '<' if d[:2] == b'II' else '>'
    if struct.unpack_from(e + 'H', d, 2)[0] != 42:
        raise ImgError('BigTIFF is not supported')
    ifd, = struct.unpack_from(e + 'I', d, 4)
    n, = struct.unpack_from(e + 'H', d, ifd)
    tags = {}
    sizes = {1: 1, 2: 1, 3: 2, 4: 4, 5: 8, 6: 1, 7: 1, 8: 2, 9: 4, 10: 8, 11: 4, 12: 8}
    fm = {1: 'B', 2: 'c', 3: 'H', 4: 'I', 6: 'b', 7: 'B', 8: 'h', 9: 'i', 11: 'f', 12: 'd'}
    for i in range(n):
        tag, typ, cnt, val = struct.unpack_from(e + 'HHI4s', d, ifd + 2 + i * 12)
        sz = sizes.get(typ, 1) * cnt
        raw = val[:sz] if sz <= 4 else d[struct.unpack(e + 'I', val)[0]:][:sz]
        if typ in fm and typ != 2:
            tags[tag] = struct.unpack(e + '%d%s' % (cnt, fm[typ]), raw[:cnt * sizes[typ]])
        else:
            tags[tag] = raw
    g = lambda t, dflt=None: (tags[t][0] if t in tags and len(tags[t]) else dflt)
    w, h = g(256), g(257)
    if not w or not h:
        raise ImgError('TIFF has no size')
    _check_dims(w, h)
    spp, comp, photo, planar, pred = g(277, 1), g(259, 1), g(262, 1), g(284, 1), g(317, 1)
    bits = tags.get(258, (1,))
    if 322 in tags or planar != 1 or len(set(bits)) != 1 or bits[0] not in (8, 16):
        raise ImgError('TIFF layout not supported by the built-in decoder')
    if comp not in (1, 5, 8, 32946, 32773) or pred not in (1, 2) or (pred == 2 and bits[0] != 8):
        raise ImgError('TIFF compression %s not supported by the built-in decoder' % comp)
    if 339 in tags and any(x not in (1,) for x in tags[339]):
        raise ImgError('floating point / signed TIFF not supported')
    bps = bits[0] // 8
    rps = min(g(278, h), h)
    offs, cnts = tags.get(273), tags.get(279)
    if not offs:
        raise ImgError('TIFF has no strips')
    rowbytes = w * spp * bps
    buf = bytearray()
    for i, o in enumerate(offs):
        rows = min(rps, h - i * rps)
        if rows <= 0:
            break
        chunk = d[o:o + (cnts[i] if cnts else len(d))]
        want = rows * rowbytes
        if comp == 5:
            s = _lzw_tiff(chunk, want)
        elif comp in (8, 32946):
            s = zlib.decompress(chunk)
        elif comp == 32773:
            s = _packbits(chunk, want)
        else:
            s = chunk
        s = bytearray(s[:want])
        if len(s) < want:
            raise ImgError('TIFF strip truncated')
        if pred == 2:
            for r in range(rows):
                base = r * rowbytes
                for c in range(spp):
                    for x in range(1, w):
                        k = base + x * spp + c
                        s[k] = (s[k] + s[k - spp]) & 255
        buf += s
    if bps == 2:  # keep the high byte of each 16-bit sample
        buf = buf[0::2] if e == '>' else buf[1::2]
    px = w * h
    out = bytearray(px * 4)
    extra = g(338, 0)
    if photo in (0, 1):
        if spp not in (1, 2):
            raise ImgError('unexpected TIFF sample count')
        gray = buf[0::spp]
        if photo == 0:
            gray = bytes(255 - x for x in gray)
        out[0::4] = out[1::4] = out[2::4] = gray
        out[3::4] = buf[1::2] if spp == 2 else b'\xff' * px
    elif photo == 2:
        if spp < 3:
            raise ImgError('unexpected TIFF sample count')
        out[0::4], out[1::4], out[2::4] = buf[0::spp], buf[1::spp], buf[2::spp]
        out[3::4] = buf[3::spp] if spp >= 4 else b'\xff' * px
    elif photo == 3:
        cm = tags.get(320)
        if not cm or bps != 1:
            raise ImgError('palette TIFF not supported')
        nn = len(cm) // 3
        pal = [bytes((cm[i] >> 8, cm[nn + i] >> 8, cm[2 * nn + i] >> 8, 255)) for i in range(nn)]
        for i in range(px):
            out[i * 4:i * 4 + 4] = pal[buf[i * spp]] if buf[i * spp] < nn else b'\0\0\0\xff'
    else:
        raise ImgError('TIFF colour model %s not supported by the built-in decoder' % photo)
    return w, h, out


IMG_MIME = {'png': 'image/png', 'jpg': 'image/jpeg', 'gif': 'image/gif', 'webp': 'image/webp', 'bmp': 'image/bmp'}


def sniff_image(d, at=0):
    """Name the image format from its first bytes (None if unknown)."""
    h = d[at:at + 16]
    if h[:8] == b'\x89PNG\r\n\x1a\n':
        return 'png'
    if h[:3] == b'\xff\xd8\xff':
        return 'jpg'
    if h[:6] in (b'GIF87a', b'GIF89a'):
        return 'gif'
    if h[:4] == b'RIFF' and d[at + 8:at + 12] == b'WEBP':
        return 'webp'
    if h[:4] == b'DDS ':
        return 'dds'
    if h[:4] in (b'II*\x00', b'MM\x00*'):
        return 'tif'
    if h[:4] in (b'II+\x00', b'MM\x00+'):
        return 'bigtiff'
    if h[:2] == b'BM' and len(d) > at + 14:
        return 'bmp'
    return None


def find_embedded_image(d):
    """Some files carry a small header before the real picture: look for a known signature early on."""
    best = None
    for sig in (b'\x89PNG\r\n\x1a\n', b'\xff\xd8\xff', b'GIF8', b'DDS ', b'II*\x00', b'MM\x00*'):
        i = d.find(sig, 1, 4096)
        if i > 0 and (best is None or i < best):
            if sniff_image(d, i):
                best = i
    return best


def to_png(data, ext):
    """Decode a TGA / TIFF / DDS file to image bytes (PNG, or the original bytes when the browser can show them).
    The file's own bytes decide the format, not its extension."""
    err = None
    kind = sniff_image(data)
    if kind is None and ext in ('tif', 'tiff', 'dds', 'tga'):
        off = find_embedded_image(data)
        if off:
            data = data[off:]
            kind = sniff_image(data)
    if kind in IMG_MIME:
        return data
    try:
        if kind in ('tif', 'dds'):
            ext = kind
        elif kind is None and ext in ('tif', 'tiff'):
            try:
                w, h, px = decode_tga(data)  # a TGA wearing a .tif name
                return png_encode(w, h, px)
            except (ImgError, struct.error, IndexError, zlib.error, ValueError):
                pass
        if ext == 'tga':
            w, h, px = decode_tga(data)
        elif ext in ('tif', 'tiff'):
            w, h, px = decode_tiff(data)
        elif ext == 'dds':
            w, h, px = decode_dds(data)
        else:
            raise ImgError('unknown image type')
        return png_encode(w, h, px)
    except (ImgError, struct.error, IndexError, zlib.error, ValueError) as ex:
        err = str(ex) or ex.__class__.__name__
        if kind is None:
            err += ' (the file starts with %s, %d bytes)' % (' '.join('%02x' % x for x in data[:12]), len(data))
    try:  # last resort: Pillow, if the user has it
        from PIL import Image
        im = Image.open(io.BytesIO(data))
        im.load()
        im = im.convert('RGBA')
        return png_encode(im.width, im.height, bytearray(im.tobytes()))
    except Exception:
        raise ImgError(err)


# ---------------------------------------------------------------- 3D models
# A ".fbx" in the package is not an Autodesk file. It is the engine's model description:
#   u8 0, u32 version, u32, u32, u32, u32 mesh_count,
#   mesh table: [u32 name_len, name, u32 material_slot, u32 vertex_count, u32 triangle_count] * mesh_count,
#   material table: u32 count, then per material: u32 name_len, name, 16 zero bytes, u32, u32,
#                   u32 tex_len, texture file name, 4 x float32 colour, u8
# The geometry itself is in the sibling '<model>.fbx.data-xbin.meta':
#   u8 0, u32 version, 8 bytes, u32 mesh_count, then per mesh:
#   [u32 name_len, name, u32 material_slot, 16 bytes, u32 float_count, floats (15 per vertex:
#    position xyz, normal xyz, 6 more floats, uv, packed colour), u32 index_count, u32 indices, u32 0]
VERT_STRIDE = 60
_model_cache = OrderedDict()
_model_lock = threading.Lock()
_png_cache = OrderedDict()
_png_lock = threading.Lock()


def _rd_str(d, p):
    n, = struct.unpack_from('<I', d, p)
    if n > 4096 or p + 4 + n > len(d):
        raise FormatError('bad string')
    return d[p + 4:p + 4 + n].decode('utf-8', 'replace'), p + 4 + n


def parse_model_desc(f):
    if len(f) < 25 or f[0] != 0:
        raise FormatError('not a model description')
    takes, = struct.unpack_from('<I', f, 13)  # animation takes: a list of names (skinned models), else 0
    p = 17
    if 0 < takes <= 1000:
        for _ in range(takes):
            _, p = _rd_str(f, p)
    n, = struct.unpack_from('<I', f, p)
    p += 4
    if n > 100000:
        raise FormatError('not a model description')
    meshes = []
    for _ in range(n):
        name, p = _rd_str(f, p)
        slot, v, t = struct.unpack_from('<III', f, p)
        p += 12
        meshes.append({'name': name, 'slot': slot, 'verts': v, 'tris': t})
    groups, nodes, tree_at = None, None, None
    for q in range(p, len(f) - 8):  # the sub-mesh list + node tree end exactly at end of file
        cnt, = struct.unpack_from('<I', f, q)
        if not 0 < cnt <= len(meshes) * 2 or q + 8 > len(f) or not 0 < struct.unpack_from('<I', f, q + 4)[0] < 200:
            continue
        try:
            groups, nodes = parse_groups(f, q, meshes)
            tree_at = q
            break
        except (struct.error, FormatError, RecursionError, IndexError):
            continue
    return meshes, parse_materials(f, p, tree_at), groups, nodes


def parse_materials(f, p, stop):
    """Material table (layout differs a little between model versions, so both are tried;
    when the end of the table is known the one that lands exactly there wins)."""
    def one(variant):
        q = p
        mc, = struct.unpack_from('<I', f, q)
        q += 4
        if mc > 10000:
            raise FormatError('bad material count')
        out = []
        for _ in range(mc):
            name, q = _rd_str(f, q)
            if variant == 0:  # newer layout: 16 extra bytes (zeros) before the texture flag
                q += 16
            flag, = struct.unpack_from('<I', f, q)
            q += 4
            tex = ''
            if flag == 1:
                q += 4
                tex, q = _rd_str(f, q)
            elif flag != 0:
                raise FormatError('unknown material layout')
            col = struct.unpack_from('<4f', f, q)
            q += 17
            if not all(-1e6 < c < 1e6 for c in col):
                raise FormatError('bad colour')
            out.append({'name': name, 'tex': tex if tex.strip('.') else '', 'color': [round(c, 3) for c in col]})
        return out, q
    first = None
    for variant in (0, 1):
        try:
            res = one(variant)
        except (struct.error, FormatError):
            continue
        if stop is None or res[1] == stop:
            return res[0]
        first = first or res[0]
    return first or []


NODE_FIXED = 108  # bytes between a node's name and its child count (guid, flags, 4x4 matrix)


def parse_groups(f, p, meshes):
    """After the material table: a list of sub-mesh entries [name, mesh index for each of 5 LODs],
    then the scene node tree (RootNode > parts > objects > sub-meshes). Returns nested groups
    [{'name', 'meshes': [indices, all LODs], 'children': [...]}]."""
    n, = struct.unpack_from('<I', f, p)
    p += 4
    if n > 100000:
        raise FormatError('bad sub-mesh list')
    sub = {}
    for _ in range(n):
        name, p = _rd_str(f, p)
        idx = tuple(i for i in struct.unpack_from('<5I', f, p) if i != 0xFFFFFFFF)  # -1: no mesh at that LOD
        p += 20
        if any(i >= len(meshes) for i in idx):
            raise FormatError('sub-mesh index out of range')
        sub[name] = idx
    if f[p] != 1:
        raise FormatError('unexpected node tree header')
    p += 1
    budget = [200000]

    def node(p, depth):
        if depth > 40 or budget[0] <= 0:
            raise FormatError('node tree too deep')
        budget[0] -= 1
        name, p = _rd_str(f, p)
        cnt, = struct.unpack_from('<I', f, p + NODE_FIXED)
        guid = str(uuid.UUID(bytes=bytes(f[p:p + 16])))
        mat = struct.unpack_from('<16f', f, p + 44)
        p += NODE_FIXED + 4
        kids = []
        for _ in range(cnt):
            k, p = node(p, depth + 1)
            kids.append(k)
        return {'name': name, 'kids': kids, 'guid': guid, 'mat': mat}, p
    root, end = node(p, 0)
    if end != len(f):
        raise FormatError('node tree does not end at end of file')
    colliders = {}
    for i, m in enumerate(meshes):
        if m['name'].endswith('_COLLIDER'):
            colliders.setdefault(m['name'][:-9], []).append(i)
    used = set()
    nodes, names = {}, {}  # node guid -> mesh indices under it / its name

    def build(nd, acc, depth):
        # acc is the product of the local matrices from this node's parent up to (not including) the top-level
        # part node, so separate parts keep their own origin and stay overlaid.
        mine = acc if depth == 1 else _mm(nd['mat'], acc)
        direct, kids = [], []
        for k in nd['kids']:
            if not k['kids'] and k['name'] in sub:
                w = _mm(k['mat'], mine)
                for i in sub[k['name']]:
                    xf.setdefault(i, w)
                direct += sub[k['name']]
                nodes[k['guid']] = list(sub[k['name']])
                names[k['guid']] = k['name']
            else:
                g = build(k, mine, depth + 1)
                if g:
                    kids.append(g)
        for i in colliders.get(nd['name'], []):
            xf.setdefault(i, mine)
        direct += colliders.get(nd['name'], [])
        allm = list(direct)
        for g in kids:
            allm += g['meshes']
        if not allm:
            return None
        used.update(allm)
        nodes[nd['guid']] = sorted(set(allm))
        names[nd['guid']] = nd['name']
        return {'name': nd['name'], 'guid': nd['guid'], 'meshes': sorted(set(allm)), 'direct': sorted(set(direct)), 'children': kids}
    xf = {}
    top = [g for g in (build(k, _IDENT, 1) for k in root['kids']) if g]
    while len(top) == 1 and top[0]['children']:  # a lone wrapper adds nothing
        top = top[0]['children']
    rest = [i for i in range(len(meshes)) if i not in used]
    if rest:
        top.append({'name': '(not in the scene tree)', 'guid': None, 'meshes': rest, 'direct': rest, 'children': []})
    nodes[root['guid']] = sorted(used)
    names[root['guid']] = root['name']
    for i, w in xf.items():
        if any(abs(a - b) > 1e-5 for a, b in zip(w, _IDENT)) and all(abs(v) < 1e7 for v in w):
            meshes[i]['xf'] = [round(v, 6) for v in w]
            det = (w[0] * (w[5] * w[10] - w[6] * w[9]) - w[1] * (w[4] * w[10] - w[6] * w[8])
                   + w[2] * (w[4] * w[9] - w[5] * w[8]))
            if det < 0:
                meshes[i]['flip'] = True
    return top, {'meshes': nodes, 'names': names}


_IDENT = (1.0, 0, 0, 0, 0, 1.0, 0, 0, 0, 0, 1.0, 0, 0, 0, 0, 1.0)


def _mm(a, b):
    """4x4 row-major product for row vectors: v * a * b."""
    return tuple(sum(a[r * 4 + k] * b[k * 4 + c] for k in range(4)) for r in range(4) for c in range(4))


def _parse_xbin_skinned(d, meshes):
    """Skinned models: the file starts with animation data, and each mesh carries a bone table,
    skin weights (23 floats per vertex instead of 15) and morph targets. Meshes are found by name."""
    out, cursor = [], 0
    for m in meshes:
        key = struct.pack('<I', len(m['name'].encode())) + m['name'].encode()
        at = d.find(key, cursor)
        if at < 0:
            raise FormatError('geometry file does not match the model description')
        p = at + len(key)
        nb, = struct.unpack_from('<I', d, p)
        p += 4
        if nb > 1000:
            raise FormatError('unexpected bone table')
        for _ in range(nb):
            _, p = _rd_str(d, p)
            p += 64  # inverse bind matrix
        p += 16
        nf, = struct.unpack_from('<I', d, p)
        vo = p + 4
        p = vo + nf * 4
        ni, = struct.unpack_from('<I', d, p)
        io_ = p + 4
        p = io_ + ni * 4
        if nf % 23 or p > len(d):
            raise FormatError('unexpected vertex layout')
        out.append((vo, nf // 23, io_, ni, 23))
        cursor = p
    return out


def parse_xbin(d, meshes):
    takes, = struct.unpack_from('<I', d, 9)  # animation takes: 0 for static models
    if takes:
        return _parse_xbin_skinned(d, meshes)
    n_expected = len(meshes)
    n, = struct.unpack_from('<I', d, 13)
    if n != n_expected:
        raise FormatError('geometry file does not match the model description')
    p, out = 17, []
    for _ in range(n):
        name, p = _rd_str(d, p)
        p += 20
        nf, = struct.unpack_from('<I', d, p)
        p += 4
        vo = p
        p += nf * 4
        ni, = struct.unpack_from('<I', d, p)
        io_ = p + 4
        p = io_ + ni * 4 + 4
        if nf % 15 or p > len(d):
            raise FormatError('unexpected vertex layout')
        out.append((vo, nf // 15, io_, ni, 15))
    return out


def basename_index(pkg):
    idx = getattr(pkg, '_base', None)
    if idx is None:
        idx = {}
        for pth, _ in pkg.files:
            idx.setdefault(pth.rsplit('/', 1)[-1].lower(), []).append(pth)
        pkg._base = idx
    return idx


def find_texture(model_pkg, model_path, fname):
    best, score = None, -1
    for pkg in [model_pkg] + [p for p in PACKS.values() if p is not model_pkg]:
        for cand in basename_index(pkg).get(fname.lower(), ()):
            a, b = cand.split('/'), model_path.split('/')
            sc = 0
            while sc < min(len(a), len(b)) and a[sc] == b[sc]:
                sc += 1
            sc += 100 if pkg is model_pkg else 0
            if sc > score:
                best, score = (pkg.name, cand), sc
    return best


TEX_SLOTS = ('AlbedoTexture', 'NormalTexture', 'MetalnessTexture', 'RoughnessTexture', 'SpecularTexture', 'GlowTexture')


def child_values(c, off):
    """{name: first value or {tag: value}} for the children of the node at offset off."""
    out = {}
    items, _ = c.page(off, 0, 400)
    for nd in items:
        fl = nd['fields']
        out[nd['name']] = fl[0]['value'] if len(fl) == 1 else {x['tag']: x['value'] for x in fl}
    return out


_color_cache = {}


_IMG_EXTS = ('png', 'jpg', 'jpeg', 'gif', 'tga', 'tif', 'tiff', 'dds')


def _image_only_icon(c):
    """Icon for the first image if every value in the file is a link to an image file (zero GUIDs and
    class names ignored); None if the file also holds strings, numbers, bools, other links, etc."""
    first, stack, seen, guard = None, [4], 0, c.dlen // 16 + 2
    while stack:
        nd = c.node(stack.pop())
        seen += 1
        if seen > guard:
            return None
        for f in nd['fields']:
            if f['type'] == 'class':
                continue
            if f['type'] != 'guid':
                return None
            if int(uuid.UUID(f['value'])) == 0:
                continue
            h = GUIDS.lookup(f['value'])
            if not h or h['sub'] or ext_of(h['path']) not in _IMG_EXTS:
                return None
            if first is None:
                first = {'icon': {'pkg': h['pkg'], 'path': h['path'], 'sub': False}}
        if nd['next']:
            stack.append(nd['next'])
        if nd['child']:
            stack.append(nd['child'])
    return first


def color_of(hit):
    """[r, g, b] if the file is a tiny asset holding a 'Color' value (e.g. HeraldryColor_*.data), else None."""
    key = (hit['pkg'], hit['path'])
    if key in _color_cache:
        return _color_cache[key]
    out = None
    pkg = PACKS.get(hit['pkg'])
    node = pkg.find(hit['path']) if pkg else None
    if isinstance(node, File) and node.len <= 8192 and not hit['sub'] and ext_of(hit['path']) not in _NOSCAN:
        try:
            data = pkg.read(node)
            if looks_like_container(data[:16], len(data)):
                c = get_container(pkg, hit['path'], node)
                root = c.node(4)
                col = child_values(c, root['child']).get('Color') if root['child'] and node.len <= 2048 else None
                if isinstance(col, dict) and all(isinstance(col.get(k), (int, float)) for k in 'rgb'):
                    out = {'color': [round(max(0.0, min(1.0, col[k])), 4) for k in 'rgb']}
                else:
                    out = _image_only_icon(c)
        except (FormatError, struct.error, KeyError, RecursionError):
            out = None
    if out or GUIDS.finished:
        _color_cache[key] = out
    return out


def material_props(pkg, path, node):
    """Decode a material .data file into plain properties; None if it is not a material."""
    if node.len > 256 * 1024:
        return None
    try:
        c = get_container(pkg, path, node)
        root = c.node(4)
        if not root['child']:
            return None
        v = child_values(c, root['child'])
    except (FormatError, struct.error, KeyError, RecursionError):
        return None
    if 'AlbedoTexture' not in v and 'AlbedoColor' not in v:
        return None
    col = v.get('AlbedoColor')
    props = {'color': [col.get(k, 1.0) for k in 'rgba'] if isinstance(col, dict) else [1, 1, 1, 1],
             'metalness': v.get('Metalness'), 'roughness': v.get('Roughness'),
             'render_mode': v.get('RenderMode'), 'alpha_test': v.get('HasAlphaTest'),
             'two_sided': v.get('BackFaceVisible'), 'shadow': v.get('HasShadow'), 'textures': {}}
    for slot in TEX_SLOTS:
        g = v.get(slot)
        if isinstance(g, str) and g != ZERO_GUID:
            props['textures'][slot] = {'guid': g, 'file': GUIDS.lookup(g)}
    return props


def resolve_materials(pkg, path, mats):
    """Attach real material files (via the model's .meta MaterialList) and their textures to each
    material of the model description; falls back to guessing the texture by file name."""
    pairs = {}
    mnode = pkg.find(path + '.meta')
    if isinstance(mnode, File) and mnode.len <= 1024 * 1024:
        try:
            c = get_container(pkg, path + '.meta', mnode)
            stack = [4]
            while stack:
                nd = c.node(stack.pop())
                if nd['next']:
                    stack.append(nd['next'])
                if nd['name'] == 'MaterialList' and nd['child']:
                    items, _ = c.page(nd['child'], 0, 1000)
                    for it in items:
                        if it['child']:
                            v = child_values(c, it['child'])
                            if v.get('MaterialName') and v.get('MaterialGuid'):
                                pairs.setdefault(v['MaterialName'].lower(), v['MaterialGuid'])
                elif nd['child']:
                    stack.append(nd['child'])
        except (FormatError, struct.error, KeyError, RecursionError):
            pass
    out = []
    for m in mats:
        m = dict(m, material=None, texture=None, normal=None)
        g = pairs.get(m['name'].lower())
        hit = GUIDS.lookup(g) if g else None
        if hit:
            mn = PACKS[hit['pkg']].find(hit['path'])
            props = material_props(PACKS[hit['pkg']], hit['path'], mn) if isinstance(mn, File) else None
            m['material'] = {'pkg': hit['pkg'], 'path': hit['path']}
            if props:
                m['color'] = [round(x, 3) for x in props['color']]
                m['alpha_test'] = bool(props['alpha_test'])
                t = props['textures'].get('AlbedoTexture')
                if t and t['file']:
                    m['texture'] = {'pkg': t['file']['pkg'], 'path': t['file']['path']}
                t = props['textures'].get('NormalTexture')
                if t and t['file']:
                    m['normal'] = {'pkg': t['file']['pkg'], 'path': t['file']['path']}
        if m['texture'] is None and m['tex']:
            h = find_texture(pkg, path, m['tex'])
            if h:
                m['texture'] = {'pkg': h[0], 'path': h[1]}
        out.append(m)
    return out


def get_model(pkg, path, node):
    key = (pkg.name, path)
    with _model_lock:
        if key in _model_cache:
            _model_cache.move_to_end(key)
            return _model_cache[key]
    if node.len > 8 * 1024 * 1024:
        raise FormatError('model description unexpectedly large')
    meshes, mats, groups, nodes = parse_model_desc(pkg.read(node))
    gnode = pkg.find(path + '.data-xbin.meta')
    geo = None
    if isinstance(gnode, File) and gnode.len <= 512 * 1024 * 1024:
        data = pkg.read(gnode)
        rngs = parse_xbin(data, meshes)
        for m, r in zip(meshes, rngs):
            if (r[1], r[3]) != (m['verts'], m['tris'] * 3):
                raise FormatError('geometry file does not match the model description')
        geo = (data, rngs)
    for m in meshes:
        tail = m['name'].rsplit('_LOD', 1)
        m['lod'] = int(tail[1]) if len(tail) == 2 and tail[1].isdigit() else 0
        m['collider'] = m['name'].endswith('_COLLIDER')
    res = (meshes, mats, geo, groups, nodes)
    with _model_lock:
        _model_cache[key] = res
        while len(_model_cache) > 2:
            _model_cache.popitem(last=False)
    return res


# ---------------------------------------------------------------- Prefabs
# A prefab is a container shaped like:  root > object (name, id, transform, components, assetId, ...)
#                                              > children > child > object / children ...
# "components" holds one node per component class (GamCCompGraphic, PlaCCompBuildingPart, ...) whose
# sub-nodes are that component's fields. Links to other files are GUID values.

def container_tree(c, off, budget, depth=0):
    if depth > 120:
        raise FormatError('nesting too deep')
    out = []
    items, _ = c.page(off, 0, 1000000)
    for nd in items:
        budget[0] -= 1
        if budget[0] < 0:
            raise FormatError('file too large for the prefab view')
        e = {'n': nd['name']}
        if nd['fields']:
            e['f'] = nd['fields']
        if nd['child']:
            e['c'] = container_tree(c, nd['child'], budget, depth + 1)
        out.append(e)
    return out


def _first(e):
    f = e.get('f')
    return f[0]['value'] if f else None


def _vec(e, keys):
    d = {x['n']: _first(x) for x in e.get('c', [])}
    return [d.get(k, 0) for k in keys]


def prefab_object(kids):
    o = {'name': None, 'id': None, 'asset': None, 'transform': None, 'flags': {}, 'components': [], 'children': []}
    for e in kids:
        if e['n'] == 'object':
            for x in e.get('c', []):
                n = x['n']
                if n == 'name':
                    o['name'] = _first(x)
                elif n == 'id':
                    o['id'] = _first(x)
                elif n == 'assetId':
                    o['asset'] = _first(x)
                elif n == 'transform':
                    sub = {y['n']: y for y in x.get('c', [])}
                    o['transform'] = {'p': _vec(sub.get('position', {}), 'xyz'), 'r': _vec(sub.get('rotation', {}), 'xyzw'),
                                      's': _vec(sub.get('scale', {}), 'xyz')} if sub else None
                elif n == 'components':
                    for comp in x.get('c', []):
                        o['components'].append({'type': comp['n'], 'f': comp.get('f'), 'c': comp.get('c', [])})
                else:
                    o['flags'][n] = _first(x)
        elif e['n'] == 'children':
            for ch in e.get('c', []):
                o['children'].append(prefab_object(ch.get('c', [])))
    return o


def prefab_of(pkg, path, node):
    """Parsed prefab (nested objects) or None if the file is not a prefab."""
    if node.len > 16 * 1024 * 1024:
        return None
    try:
        c = get_container(pkg, path, node)
        root = c.node(4)
        if root['name'] != 'root' or not root['child']:
            return None
        names = [x['name'] for x in c.page(root['child'], 0, 8)[0]]
        if 'object' not in names:
            return None
        tree = container_tree(c, root['child'], [60000])
        return prefab_object(tree)
    except (FormatError, struct.error, KeyError, RecursionError):
        return None


# ---------------------------------------------------------------- Server helpers
MIME = {'png': 'image/png', 'jpg': 'image/jpeg', 'jpeg': 'image/jpeg', 'gif': 'image/gif',
        'webm': 'video/webm', 'otf': 'font/otf', 'ttf': 'font/ttf', 'txt': 'text/plain; charset=utf-8'}
IMAGE_EXT = {'png', 'jpg', 'jpeg', 'gif'}
UNSUPPORTED_IMAGE_EXT = {'tga', 'tif', 'tiff', 'dds'}


def ext_of(name):
    return name.rsplit('.', 1)[-1].lower() if '.' in name else ''


def kind_of(pkg, name, fl):
    head = pkg.read(fl, 0, 4096)
    ext = ext_of(name)
    if looks_like_container(head, fl.len):
        return 'container'
    if ext in IMAGE_EXT: return 'image'
    if ext in UNSUPPORTED_IMAGE_EXT: return 'image-conv'
    if ext == 'webm': return 'video'
    if ext in ('otf', 'ttf'): return 'font'
    if ext == 'fbx':
        return 'model' if len(head) > 24 and head[0] == 0 and fl.len < 8 * 1024 * 1024 else 'binary'
    if head and b'\0' not in head:
        try:
            head.decode('utf-8')
            return 'text'
        except UnicodeDecodeError:
            try:
                head[:-3].decode('utf-8')
                return 'text'
            except UnicodeDecodeError:
                pass
    return 'binary'


def hexdump(b, base):
    out = []
    for i in range(0, len(b), 16):
        c = b[i:i + 16]
        out.append('%08x  %-47s  %s' % (base + i, ' '.join('%02x' % x for x in c),
                                       ''.join(chr(x) if 32 <= x < 127 else '.' for x in c)))
    return '\n'.join(out)


# ---------------------------------------------------------------- HTTP server
class Handler(BaseHTTPRequestHandler):
    server_version = 'PackageBrowser/2'

    def log_message(self, *a):
        pass

    def send_json(self, obj, code=200):
        body = json.dumps(obj).encode()
        self.send_response(code)
        self.send_header('Content-Type', 'application/json')
        self.send_header('Content-Length', str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def err(self, msg, code=400):
        self.send_json({'error': msg}, code)

    def target(self, q):
        pkg = PACKS.get(q.get('pkg', ''))
        if not pkg:
            return None, None, 'unknown package'
        node = pkg.find(q.get('path', ''))
        if node is None:
            return None, None, 'not found'
        return pkg, node, None

    def file_target(self, q):
        pkg, node, e = self.target(q)
        if e or not isinstance(node, File):
            self.err(e or 'not a file', 404)
            return None, None
        return pkg, node

    def do_GET(self):
        u = urlparse(self.path)
        q = {k: v[0] for k, v in parse_qs(u.query).items()}
        try:
            if u.path == '/':
                body = PAGE.encode()
                self.send_response(200)
                self.send_header('Content-Type', 'text/html; charset=utf-8')
                self.send_header('Content-Length', str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            elif u.path == '/api/roots':
                want = want_exts(q)
                self.send_json([{'pkg': p.name, 'files': len(p.files), 'size': p.size} for p in PACKS.values()
                                if not want or want & dir_exts(p.root)])
            elif u.path == '/api/exts':
                counts = {}
                for p in PACKS.values():
                    for pth, _ in p.files:
                        e = file_ext(pth.rsplit('/', 1)[-1])
                        counts[e] = counts.get(e, 0) + 1
                self.send_json(sorted(({'ext': k, 'count': v} for k, v in counts.items()),
                                      key=lambda x: (-x['count'], x['ext'])))
            elif u.path == '/api/ls':
                pkg, node, e = self.target(q)
                if e or not isinstance(node, Dir):
                    return self.err(e or 'not a folder', 404)
                want = want_exts(q)
                nometa = q.get('nometa') == '1'
                dirs = sorted((k for k, v in node.kids.items() if isinstance(v, Dir) and (not want or want & dir_exts(v))
                               and (not nometa or dir_exts(v) - {'meta'})),
                              key=str.lower)
                files = sorted(({'name': k, 'size': v.len} for k, v in node.kids.items()
                                if isinstance(v, File) and (not want or file_ext(k) in want)
                                and not (nometa and file_ext(k) == 'meta')),
                               key=lambda x: x['name'].lower())
                self.send_json({'dirs': dirs, 'files': files})
            elif u.path == '/api/search':
                terms = q.get('q', '').lower().split()
                want = want_exts(q)
                nometa = q.get('nometa') == '1'
                res = []
                if terms:
                    for p in PACKS.values():
                        for (lp, path), (_, fl) in zip(p.lower, p.files):
                            if all(t in lp for t in terms) and (not want or file_ext(lp.rsplit('/', 1)[-1]) in want) \
                                    and not (nometa and lp.endswith('.meta')):
                                res.append({'pkg': p.name, 'path': path, 'size': fl.len})
                                if len(res) >= 300:
                                    break
                        if len(res) >= 300:
                            break
                self.send_json({'results': res, 'truncated': len(res) >= 300})
            elif u.path == '/api/info':
                pkg, node = self.file_target(q)
                if node is None:
                    return
                name = q['path'].rsplit('/', 1)[-1]
                kind = kind_of(pkg, name, node)
                is_mat = kind == 'container' and material_props(pkg, q['path'], node) is not None
                is_prefab = kind == 'container' and not is_mat and prefab_of(pkg, q['path'], node) is not None
                self.send_json({'name': name, 'size': node.len, 'ext': ext_of(name), 'kind': kind, 'material': is_mat,
                                'prefab': is_prefab})
            elif u.path == '/api/model':
                pkg, node = self.file_target(q)
                if node is None:
                    return
                meshes, mats, geo, groups, nodes = get_model(pkg, q['path'], node)
                rel = {}
                for suffix in ('.meta', '.prefab.meta', '.data-xbin.meta'):
                    if isinstance(pkg.find(q['path'] + suffix), File):
                        rel[suffix] = q['path'] + suffix
                self.send_json({'meshes': meshes, 'materials': resolve_materials(pkg, q['path'], mats),
                                'has_geometry': geo is not None, 'related': rel, 'groups': groups or [], 'nodes': (nodes or {}).get('meshes', {}), 'nodes_named': (nodes or {}).get('names', {}),
                                'links_ready': GUIDS.finished})
            elif u.path == '/api/mesh':
                pkg, node = self.file_target(q)
                if node is None:
                    return
                meshes, mats, geo, groups, nodes = get_model(pkg, q['path'], node)
                if geo is None:
                    return self.err('this model has no geometry file next to it', 404)
                i = int(q.get('i', '-1'))
                if not 0 <= i < len(meshes):
                    return self.err('bad mesh index')
                data, rngs = geo
                vo, nv, io_, ni, nfl = rngs[i]
                if nfl == 15:
                    verts = data[vo:vo + nv * VERT_STRIDE]
                else:  # skinned: keep the 15 static floats of each vertex, drop the skin weights
                    step = nfl * 4
                    verts = b''.join(data[vo + k * step:vo + k * step + VERT_STRIDE] for k in range(nv))
                body = struct.pack('<II', nv, ni) + verts + data[io_:io_ + ni * 4]
                self.send_response(200)
                self.send_header('Content-Type', 'application/octet-stream')
                self.send_header('Content-Length', str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            elif u.path == '/api/png':
                pkg, node = self.file_target(q)
                if node is None:
                    return
                ext = ext_of(q['path'])
                if ext not in UNSUPPORTED_IMAGE_EXT or node.len > 256 * 1024 * 1024:
                    return self.err('not a convertible image', 400)
                key = (pkg.name, q['path'])
                with _png_lock:
                    body = _png_cache.get(key)
                    if body is not None:
                        _png_cache.move_to_end(key)
                if body is None:
                    try:
                        body = to_png(pkg.read(node), ext)
                    except ImgError as ex:
                        return self.err('Could not decode this %s image: %s' % (ext.upper(), ex), 415)
                    with _png_lock:
                        _png_cache[key] = body
                        while len(_png_cache) > 6:
                            _png_cache.popitem(last=False)
                self.send_response(200)
                self.send_header('Content-Type', IMG_MIME.get(sniff_image(body), 'image/png'))
                self.send_header('Content-Length', str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            elif u.path == '/api/tree':
                pkg, node = self.file_target(q)
                if node is None:
                    return
                if node.len > 16 * 1024 * 1024:
                    return self.err('file too large for the overview', 400)
                try:
                    c = get_container(pkg, q['path'], node)
                    root = c.node(4)
                    tree = container_tree(c, 4, [80000]) if True else None
                except (FormatError, struct.error, KeyError, RecursionError) as ex:
                    return self.err('could not read this file: %s' % ex, 415)
                self.send_json({'tree': tree})
            elif u.path == '/api/prefab':
                pkg, node = self.file_target(q)
                if node is None:
                    return
                pf = prefab_of(pkg, q['path'], node)
                if pf is None:
                    return self.err('not a prefab file', 404)
                rel = None
                if q['path'].endswith('.prefab.meta') and isinstance(pkg.find(q['path'][:-len('.prefab.meta')]), File):
                    rel = q['path'][:-len('.prefab.meta')]
                self.send_json({'root': pf, 'model': rel, 'links_ready': GUIDS.finished})
            elif u.path == '/api/links':
                pkg, node = self.file_target(q)
                if node is None:
                    return
                uses, unres = links_uses(pkg, q['path'])
                out = {'uses': uses, 'unresolved': unres, 'links_ready': GUIDS.finished}
                if q.get('only') != 'uses':
                    out['used_by'] = links_used_by(pkg, q['path']) if REFS.finished else []
                    out['used_by_ready'] = REFS.finished
                    out['progress'] = [REFS.done, REFS.total]
                self.send_json(out)
            elif u.path == '/api/reach':
                pkg, node = self.file_target(q)
                if node is None:
                    return
                self.send_json({'models': links_reach(pkg, q['path']), 'links_ready': GUIDS.finished})
            elif u.path == '/api/material':
                pkg, node = self.file_target(q)
                if node is None:
                    return
                props = material_props(pkg, q['path'], node)
                if props is None:
                    return self.err('not a material file', 404)
                for t in props['textures'].values():
                    t['file'] = GUIDS.lookup(t['guid'])
                props['links_ready'] = GUIDS.finished
                self.send_json(props)
            elif u.path == '/api/nodes':
                pkg, node = self.file_target(q)
                if node is None:
                    return
                try:
                    c = get_container(pkg, q['path'], node)
                    items, nxt = c.page(int(q.get('at', '4')), int(q.get('skip', '0')), 200)
                except (FormatError, struct.error, ValueError) as ex:
                    return self.err('could not decode: %s' % ex)
                self.send_json({'items': [{'name': n['name'], 'child': n['child'], 'fields': n['fields']} for n in items],
                                'next': nxt})
            elif u.path == '/api/guids':
                ids = [i for i in q.get('ids', '').split(',') if i]
                found = {}
                for i in ids[:500]:
                    hit = GUIDS.lookup(i)
                    if hit:
                        hit.update(color_of(hit) or {})
                        found[i] = hit
                self.send_json({'finished': GUIDS.finished, 'done': GUIDS.done, 'total': GUIDS.total,
                                'refs_finished': REFS.finished, 'refs_done': REFS.done, 'refs_total': REFS.total,
                                'indexed': len(GUIDS.map), 'found': found})
            elif u.path == '/api/text':
                pkg, node = self.file_target(q)
                if node is None:
                    return
                data = pkg.read(node, 0, 1024 * 1024)
                self.send_json({'text': data.decode('utf-8', 'replace'), 'truncated': node.len > len(data)})
            elif u.path == '/api/hex':
                pkg, node = self.file_target(q)
                if node is None:
                    return
                off = max(0, int(q.get('offset', '0')))
                data = pkg.read(node, off, 4096)
                self.send_json({'hex': hexdump(data, off), 'next': off + len(data) if off + len(data) < node.len else None})
            elif u.path == '/api/raw':
                self.raw(q)
            else:
                self.err('not found', 404)
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as ex:  # never crash the server on one bad request
            try:
                self.err('server error: %s' % ex, 500)
            except Exception:
                pass

    def raw(self, q):
        pkg, node = self.file_target(q)
        if node is None:
            return
        name = q['path'].rsplit('/', 1)[-1]
        ctype = MIME.get(ext_of(name)) or mimetypes.guess_type(name)[0] or 'application/octet-stream'
        start, end = 0, node.len - 1
        code = 200
        rng = self.headers.get('Range')
        if rng and rng.startswith('bytes=') and node.len:
            a, _, b = rng[6:].split(',')[0].partition('-')
            try:
                if a == '':
                    start = max(0, node.len - int(b))
                else:
                    start = int(a)
                    if b:
                        end = min(int(b), node.len - 1)
                if start > end or start >= node.len:
                    self.send_response(416)
                    self.send_header('Content-Range', 'bytes */%d' % node.len)
                    self.end_headers()
                    return
                code = 206
            except ValueError:
                start, end = 0, node.len - 1
        length = end - start + 1 if node.len else 0
        self.send_response(code)
        self.send_header('Content-Type', ctype)
        self.send_header('Accept-Ranges', 'bytes')
        self.send_header('Content-Length', str(length))
        if code == 206:
            self.send_header('Content-Range', 'bytes %d-%d/%d' % (start, end, node.len))
        self.end_headers()
        with open(pkg.path, 'rb') as f:
            f.seek(pkg.data_off + node.off + start)
            left = length
            while left > 0:
                chunk = f.read(min(1 << 20, left))
                if not chunk:
                    break
                self.wfile.write(chunk)
                left -= len(chunk)


# ---------------------------------------------------------------- Web page (HTML, CSS and JS served at /)
PAGE = r'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><title>Package browser</title>
<meta name="viewport" content="width=device-width,initial-scale=1">
<style>
:root{color-scheme:light dark;--hdr:light-dark(#4a5365,color-mix(in srgb,var(--pane) 82%,#000));--box:#e6e9ee;--bg:#fff;--fg:#1d2127;--mut:#6b7480;--line:#d9dde3;--sel:#e4efff;--acc:#1f6feb;--pane:#f6f7f9;--guid:#a14a00;--num:#0a6b3d;--str:#7a2e8e;--bool:#b3261e}
@media(prefers-color-scheme:dark){:root{--box:#2a2e36;--bg:#16181c;--fg:#e6e8eb;--mut:#8b94a1;--line:#2c3037;--sel:#233149;--acc:#6aa5ff;--pane:#1d2025;--guid:#f0a35e;--num:#6fd39c;--str:#d79bec;--bool:#ff8d85}}
*{box-sizing:border-box}html,body{height:100%;margin:0}
body{background:var(--bg);color:var(--fg);font:14px/1.4 system-ui,sans-serif;display:flex;flex-direction:column}
#app{display:flex;align-items:center;gap:14px;padding:0 18px;height:46px;flex:0 0 auto;background:var(--pane);border-bottom:1px solid var(--line)}
#app h1{margin:0;font-size:16px;font-weight:650;letter-spacing:.01em}#app .sub{color:var(--mut);font-size:12.5px;flex:1;min-width:0;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
#idx{font-size:12px;padding:3px 10px;border-radius:999px;border:1px solid var(--line);color:var(--mut);white-space:nowrap}#idx.ok{color:var(--num);border-color:currentColor}#idx.busy{color:var(--acc);border-color:currentColor}
#cols{flex:1;display:flex;min-height:0}
.ptitle{padding:6px 12px;font-size:11.5px;font-weight:650;letter-spacing:.08em;text-transform:uppercase;color:var(--mut);border-bottom:1px solid var(--line);background:var(--pane);flex:0 0 auto}
#main>.ptitle{background:var(--bg)}
#side{width:380px;min-width:240px;max-width:60vw;border-right:1px solid var(--line);display:flex;flex-direction:column;resize:horizontal;overflow:auto;background:var(--pane)}
#side header{padding:10px;border-bottom:1px solid var(--line);position:sticky;top:0;background:var(--pane);z-index:1}
#q{width:100%;padding:7px 9px;border:1px solid var(--line);border-radius:6px;background:var(--bg);color:var(--fg)}
#tree,#results{padding:6px 4px 30px}
ul{list-style:none;margin:0;padding-left:14px}#tree>ul,#results>ul{padding-left:0}
.row{padding:2px 6px;border-radius:4px;cursor:pointer;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.row:hover{background:var(--sel)}.row.sel{background:var(--sel);outline:1px solid var(--acc)}
.row .sz{color:var(--mut);font-size:12px;margin-left:8px}.dir{font-weight:600}
#main{flex:1;display:flex;flex-direction:column;min-width:0}
#top{padding:10px 16px;border-bottom:1px solid var(--line);display:flex;gap:10px;align-items:flex-start}
#top>div{flex:1;min-width:0}
#back{border:1px solid var(--line);background:var(--pane);color:var(--fg);border-radius:6px;padding:3px 9px;cursor:pointer}
#title{font-weight:600;word-break:break-all}#meta{color:var(--mut);font-size:12px;margin-top:2px}
#tabs{display:flex;gap:6px;padding:8px 16px 0;border-bottom:1px solid var(--line);align-items:center}
#tabs button,.btn{border:1px solid var(--line);background:var(--pane);color:var(--fg);padding:4px 10px;border-radius:6px 6px 0 0;cursor:pointer}
.btn{border-radius:6px;margin:4px 6px 8px 0;padding:3px 9px}
#tabs button.on{background:var(--bg);border-bottom-color:var(--bg);font-weight:600}
.lrow>summary{cursor:pointer;padding:2px 0}.lbody{margin-left:18px;border-left:1px solid var(--line);padding-left:8px}
.thumb3d{width:240px;height:170px;border-radius:6px;background:#2b3038;color:#9aa3ad;display:flex;align-items:center;justify-content:center;font-size:12px;overflow:hidden}.thumb3d img{width:100%;height:100%;display:block}.reachrow{display:flex;flex-wrap:wrap;gap:14px}.rcard{width:240px}.rcard .tg{font-size:11.5px;word-break:break-word}.reach{margin:8px 0 14px}
#tabs a{color:var(--acc);font-size:13px;margin-left:10px}#tabs a.first{margin-left:auto}
#body{flex:1;overflow:auto;padding:14px 16px}
pre{margin:0;font:12.5px/1.45 ui-monospace,Menlo,Consolas,monospace;white-space:pre-wrap;word-break:break-all}
.note{color:var(--mut);padding:20px 0}
img.pv{display:block;max-width:100%;max-height:calc(100vh - 300px);width:auto;height:auto;cursor:zoom-in;background:repeating-conic-gradient(#8883 0 25%,#0000 0 50%) 0 0/16px 16px;border:1px solid var(--line)}
details{margin-left:16px}summary{cursor:pointer;margin-left:-16px}.leaf{margin-left:16px}
.leaf,summary{font-family:ui-monospace,Menlo,Consolas,monospace;font-size:12.5px}
.nm{font-weight:600}.t-guid{color:var(--guid)}.t-float,.t-double,.t-int,.t-int64,.t-uint,.t-uint64{color:var(--num)}.t-string,.t-class{color:var(--str)}.t-bool{color:var(--bool)}
.link{color:var(--acc);text-decoration:underline;cursor:pointer}.link:hover{background:var(--sel)}.nolink{cursor:copy}
.ty{color:var(--mut);font-size:11px;margin-left:6px}.tg{color:var(--mut)}
.res .p{color:var(--mut);font-size:12px}
.mv{display:flex;gap:16px;flex-wrap:wrap;align-items:flex-start}.mvc{flex:1 1 520px;min-width:300px}.mvp{flex:0 0 420px;width:420px;min-width:0;max-width:100%;overflow:hidden}
.mvc canvas{width:100%;height:540px;border:1px solid var(--line);border-radius:6px;background:#2b3038;touch-action:none;display:block}
.mvp h4{margin:14px 0 4px}.mvctl{line-height:2}.mvlist{max-height:260px;overflow:auto;border:1px solid var(--line);border-radius:6px;padding:4px 6px;font-size:12.5px}
.mrow{display:block;padding:1px 0;word-break:break-all}.sw{display:inline-block;width:10px;height:10px;border-radius:2px;margin:0 6px 0 4px;vertical-align:baseline}
table.mt{border-collapse:collapse;font-size:12.5px}table.mt td,table.mt th{border:1px solid var(--line);padding:2px 8px;text-align:left}
.mvc canvas{touch-action:none}
#fwrap{padding:6px 10px 0}img.ico{height:22px;max-width:44px;object-fit:contain;vertical-align:middle;margin:0 6px 0 0;border:1px solid #0004;border-radius:3px;background:repeating-conic-gradient(#8885 0 25%,#0000 0 50%) 0 0/8px 8px;position:relative;transition:transform .12s;transform-origin:left center}img.ico:hover{transform:scale(5);z-index:20;box-shadow:0 4px 14px #0007}
.imgv{position:relative;display:inline-block;max-width:100%}.imgstage{overflow:hidden;max-width:100%}
.imgzoom{position:absolute;top:8px;right:8px;opacity:0;transition:opacity .12s;border:1px solid #fff4;background:#14161acc;color:#fff;border-radius:7px;padding:4px 10px;cursor:pointer;font:inherit;font-size:12.5px}
.imgv:hover .imgzoom,.imgzoom:focus{opacity:1}.imgv.nofit .imgzoom{display:none}.imgv.nofit img.pv{cursor:default}
.imgv.full{display:block}.imgv.full .imgstage{overflow:auto;max-height:calc(100vh - 300px)}.imgv.full img.pv{max-width:none;max-height:none;cursor:zoom-out}

.ov{max-width:1100px}.ovbar{margin-bottom:8px;font-size:13px;color:var(--mut)}.ovhead{font-size:16px;margin:2px 0 8px}
.ovsec{margin:0 0 16px;border:1px solid var(--line);border-radius:8px;background:var(--bg)}.ovsh{padding:8px 16px;margin:0;font-weight:600;background:var(--pane);border-bottom:1px solid var(--line);border-radius:8px 8px 0 0}.ovst{font-size:12px;letter-spacing:.06em;text-transform:uppercase}
.ovbody{padding:12px 16px}.ovbody>*+*{margin-top:14px}.ovbody>.ovsec+.ovsec{margin-top:0}.ovbody .ovsec{margin-left:0}.ovsec>.ovbody,.ovsec>.ovtextbody,.ovsec>.ovrows,.ovsec>.ovcolors,.ovsec>.ovflags,.ovsec>.ovlist,.ovsec>.ovgrid{padding:14px 18px}
.ovrows{display:grid;grid-template-columns:minmax(120px,max-content) 1fr;column-gap:18px;row-gap:9px;align-items:center}.ovrow{display:contents}.ovlabel{color:var(--fg);opacity:.9;font-weight:500}
.ovbox{display:block;border:1px solid var(--line);background:var(--pane);border-radius:6px;padding:4px 10px;min-height:28px}.ovkey{font-family:ui-monospace,Consolas,monospace;font-size:13px}.ovmuted{color:var(--mut)}.ovtable{border:1px solid var(--line);border-radius:8px;margin-top:6px}.ovtr{padding:6px 10px;border-bottom:1px solid var(--line)}.ovtr:last-child{border-bottom:0}.ovtr .ovbox{border:0;background:transparent;padding:0;min-height:0}.ovtr .ovnum{display:block}.ovlistblock{margin:0}.ovtextbody>*+*{margin-top:14px}.ovplainlist{display:flex;flex-direction:column;gap:5px}.ovplain{padding:0}.ovtext{font-weight:500}.ovnum{font-variant-numeric:tabular-nums;color:var(--num);font-weight:600}
.ovcolors{display:flex;flex-wrap:wrap;gap:16px}.ovcolor .ovlabel{margin-bottom:3px;font-size:12.5px}
.cbox{position:relative;width:96px;height:48px;border-radius:7px;border:1px solid #0005;overflow:hidden;background:repeating-conic-gradient(#b9bec6 0 25%,#fff 0 50%) 0 0/14px 14px}.cbox.big{width:150px;height:80px}.cfill{position:absolute;inset:0}
.ovgrid .cwrap{display:inline-block;margin:0 14px 12px 0}.ctext{font-size:12px;color:var(--mut);margin-top:3px;max-width:230px}.ctext b{color:var(--fg);font-family:ui-monospace,Consolas,monospace}
.ovflags{display:flex;flex-direction:column;gap:7px}.flag{display:flex;align-items:center;gap:9px;font-size:13.5px}.flag .fl{width:16px;text-align:center;font-weight:700}.flag.on .fl{color:#1f9d55}.flag.off{opacity:.8}.flag.off .fl{color:#c0392b}
.pill.on{background:#1f9d5522;color:#1f9d55}.pill.off{color:var(--mut)}
.ovgrid{display:flex;flex-wrap:wrap;gap:10px}.ovgrid .chip{display:inline-flex;flex-direction:column;align-items:center;gap:4px;width:118px;padding:8px 6px;border:1px solid var(--line);border-radius:8px;text-align:center;word-break:break-word;font-size:12px;background:var(--pane)}
.ov img.ico{height:54px;max-width:96px;margin:0}.ov .chip .sw{width:54px!important;height:30px!important;border-radius:6px!important;margin:0!important}.ov .ovrow .chip img.ico{height:30px;margin-right:6px}.ov .ovrow .chip .sw{width:22px!important;height:22px!important;margin:0 6px -6px 0!important}
.ovchips{display:flex;flex-direction:column;align-items:flex-start;gap:8px}.ovchip{border:1px solid var(--line);border-radius:6px;padding:3px 10px;background:var(--pane)}
.ovkvrow{display:grid;grid-template-columns:230px 1fr;gap:6px 16px;padding:12px 0;border-bottom:1px dashed var(--line)}.ovkvrow:last-child{border-bottom:0}.ovkv .ovbody{padding:0}.ovkv .ovrows{padding:0;grid-template-columns:minmax(90px,max-content) 1fr}.ovcard .ovbody{padding:0}.ovcard .ovrows{grid-template-columns:minmax(110px,max-content) 1fr}
.ovcard{border:1px solid var(--line);border-radius:8px;padding:14px 18px;margin:0 0 16px}.ovcard .ovbody>*+*{margin-top:14px}.ovcard .ovflags{padding:0}.ovcardhead{font-size:11.5px;color:var(--mut);margin-bottom:10px}

.pfo{border:1px solid var(--line);border-radius:8px;margin:0 0 12px;background:var(--bg)}.pfoh{display:flex;align-items:center;gap:12px;flex-wrap:wrap;padding:9px 16px;background:var(--pane);border-bottom:1px solid var(--line);border-radius:8px 8px 0 0}.pfoh b{font-size:14.5px}
.pfob{padding:12px 16px}.pfob>*+*{margin-top:12px}.pfc{padding:4px 0 6px 14px;border-left:3px solid var(--acc)}.pfch{font-weight:600;font-size:12px;letter-spacing:.06em;text-transform:uppercase;margin-bottom:8px;color:var(--fg)}
.pfkids{margin:14px 0 2px 10px;padding-left:16px;border-left:2px dashed var(--line)}.pf .ovbody{padding:0}.pf .ovbody>*+*{margin-top:10px}.pf .ovtable{margin-top:4px}
#sg,#st{font-size:13px;cursor:pointer;user-select:none;white-space:nowrap}#sg{margin-left:auto}#st{margin-left:14px}#sg input,#st input{margin-right:5px}.vtype{display:none}body.showtypes .vtype{display:inline;font-size:11px;font-weight:400;color:var(--mut);margin-left:8px;font-family:system-ui,sans-serif;letter-spacing:0}
#tbar{display:flex;align-items:center;justify-content:space-between;gap:8px;margin:0 0 6px}#hm{font-size:13px;cursor:pointer;user-select:none}.tbtns{display:flex;gap:4px}.tbtns .btn{margin:0;border-radius:6px;padding:2px 8px}#hm input{margin-right:6px}#fbtn{margin:0;border-radius:6px;width:100%;text-align:left;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}#fbtn.on{border-color:var(--acc);color:var(--acc)}
#fpanel{border:1px solid var(--line);border-radius:6px;margin-top:4px;padding:6px 8px;background:var(--bg)}
#fpanel .fl{max-height:300px;overflow:auto;margin-top:4px;display:grid;grid-template-columns:1fr 1fr;column-gap:12px}.fi{display:block;padding:1px 0;cursor:pointer}
.mvbar{margin:4px 0}.mvbar .btn{margin:0 6px 4px 0;border-radius:6px}.mvtree{max-height:460px}.mvtree summary{font-family:inherit;font-size:13px;display:flex;align-items:center;gap:4px;list-style:none;white-space:nowrap}.mvtree summary::-webkit-details-marker{display:none}.mvtree summary .nm{flex:1 1 auto;min-width:0;overflow:hidden;text-overflow:ellipsis}.mvtree summary .tg,.mvtree summary .link,.mvtree summary .ar{flex:none}.mvtree summary .ar{width:12px;color:var(--mut)}.mvtree details{margin-left:0}.mvtree .nm{font-weight:600}.grow{white-space:nowrap}.grow .link{font-size:12px}
.texrow{margin:6px 0;word-break:break-all}img.thumb{max-width:160px;max-height:160px;border:1px solid var(--line);margin-top:3px;background:repeating-conic-gradient(#8883 0 25%,#0000 0 50%) 0 0/12px 12px}
table.mt th{font-weight:600;color:var(--mut)}
.cv{position:relative}.cv canvas{display:block}.cvbar{position:absolute;top:10px;left:10px;display:flex;gap:8px;flex-wrap:wrap}.seg{display:inline-flex;border:1px solid #ffffff40;border-radius:7px;overflow:hidden;background:#14161acc}.seg button{border:0;background:transparent;color:#d8dde4;padding:4px 11px;cursor:pointer;font:inherit;font-size:12.5px}.seg button:hover{background:#ffffff1f}.seg button.on{background:#3d6fd1;color:#fff}
.chip{font-family:ui-monospace,Menlo,Consolas,monospace;font-size:12px;border-radius:4px;padding:0 4px;background:var(--pane);border:1px solid var(--line)}.chip.link{border-color:var(--acc)}
.pill{display:inline-block;font-size:11px;border-radius:9px;padding:0 7px;margin-left:6px;background:var(--sel);color:var(--fg);font-weight:400}.pill.off{background:#b3261e33}
.pfhead{margin-bottom:10px}.pfpills{margin:6px 0 4px}.pfpills .pill{margin:0 6px 4px 0}.pflinks{margin:6px 0 10px;margin-left:0}.pflinks summary{margin-left:0;font-weight:600}
details.obj>summary,details.comp>summary{font-family:inherit;font-size:13px}details.obj>summary .nm{font-weight:600}details.comp{margin-left:0}.objbody{margin-left:6px;padding-left:12px;border-left:1px solid var(--line)}
details.comp>summary .nm{color:var(--acc)}details.comp>div{padding-left:14px}

/* overview v2: sharp corners, fewer outlines, type colours */
.ov *,.pf *,.ov,.pf{border-radius:0!important}
.ovsec{border:0;background:transparent;border-left:2px solid color-mix(in srgb,var(--mut) 40%,transparent);margin-bottom:14px}
.ovsec>.ovsh{border:0;background:var(--pane)}
.ovsec.k-col{border-left-color:color-mix(in srgb,#d6409f 40%,transparent)}.ovsec.k-str{border-left-color:color-mix(in srgb,var(--str) 40%,transparent)}.ovsec.k-num{border-left-color:color-mix(in srgb,var(--num) 40%,transparent)}.ovsec.k-flag{border-left-color:color-mix(in srgb,var(--bool) 40%,transparent)}.ovsec.k-guid{border-left-color:color-mix(in srgb,var(--guid) 40%,transparent)}.ovsec.k-oth{border-left-color:color-mix(in srgb,var(--mut) 40%,transparent)}.ovsec.k-grp{border-left-color:color-mix(in srgb,var(--acc) 40%,transparent)}
.ovsec.k-col>.ovsh .ovst{color:#d6409f}.ovsec.k-str>.ovsh .ovst{color:var(--str)}.ovsec.k-num>.ovsh .ovst{color:var(--num)}.ovsec.k-flag>.ovsh .ovst{color:var(--bool)}.ovsec.k-guid>.ovsh .ovst{color:var(--guid)}.ovsec.k-grp>.ovsh .ovst{color:var(--acc)}
.ov .ovbox{border:0;background:var(--pane);color:var(--str)}.ov .ovbox.ovkey{color:var(--str)}.ov .ovbox.ovmuted{color:var(--mut)}
.ov .ovtable{border:1px solid var(--line)}
.ov .ovcard,.pf .ovcard{border:0;background:var(--pane)}
.ov .chip,.ov .ovchip,.pf .chip{border:0;background:var(--pane)}.ov .chip.link,.pf .chip.link{color:var(--guid)}
.ov .pill,.pf .pill{background:var(--pane)}.ov .pill.on{color:var(--num)}.ov .pill.off,.pf .pill.off{color:var(--bool);background:var(--pane)}.ov .pill:not(.on):not(.off),.pf .pill:not(.on):not(.off){color:var(--str)}
.ov .cbox{border:0;box-shadow:0 0 0 1px #0002}
.ov .ovgrid .chip{border:0}
.pfo{border:0;background:transparent;border-left:2px solid color-mix(in srgb,var(--acc) 40%,transparent)}.pfo>.pfoh{border:0;background:var(--pane)}
.pfc{border-left:2px solid color-mix(in srgb,var(--str) 40%,transparent)}.pfch{color:var(--str)}
.pfkids{border-left:2px solid var(--line)}
/* value boxes: darker than headers */
.ov .ovbox,.pf .ovbox{background:var(--box)}
.ov .ovtr .ovbox,.pf .ovtr .ovbox{background:transparent}
.ovrow>.ovnum,.ovrow>.pill,.ovrow>.chip,.ovrow>.tg,.ovrow>span.ovnum,.ovrow>.wch{display:flex;align-items:center;box-sizing:border-box;background:var(--box);padding:4px 10px;min-height:28px;margin:0;font-size:inherit}
.ovrow>.chip{font-size:12.5px}
.ovrow>.pill{font-weight:600}
.ov .ovrow .chip,.pf .ovrow .chip{background:var(--box)}
.ovrow>.tg{color:var(--mut)}
details.ovfold>summary{cursor:pointer;list-style:none}details.ovfold>summary::-webkit-details-marker{display:none}
details.ovfold>summary::before{content:'▸';display:inline-block;width:16px;color:var(--mut)}details.ovfold[open]>summary::before{content:'▾'}
details.ovfold.pfo>summary{display:flex}
.ovsec>.ovflagtbl,.ovsec>.ovtable{margin:14px 18px}.ovflagtbl .ovtable{margin-top:4px}.ovsub{font-size:11.5px;letter-spacing:.06em;text-transform:uppercase;color:var(--bool);margin-top:2px}.ovtr .flag{margin:0}details.ovfold>summary{font-family:inherit}details.pfc>summary.pfch{cursor:pointer;display:flex;align-items:center}details.pfc>summary.pfch::before{margin-left:-2px}
.ovbody>.ovrows{grid-template-columns:minmax(200px,max-content) 1fr}
.v-text{box-shadow:inset 3px 0 color-mix(in srgb,var(--str) 45%,transparent)}.v-num,.v-vec,.v-struct-inline{box-shadow:inset 3px 0 color-mix(in srgb,var(--num) 45%,transparent)}.v-link{box-shadow:inset 3px 0 color-mix(in srgb,var(--guid) 50%,transparent)}.v-class,.v-other{box-shadow:inset 3px 0 color-mix(in srgb,var(--mut) 45%,transparent)}
.ovbody>.ovtable{margin:0}.ovbody>.ovflagtbl2{margin-top:14px}

/* compact + unified dropdown headers */
.ovbody{padding:8px 12px}.ovbody>*+*{margin-top:8px}
.ovsec>.ovbody,.ovsec>.ovtextbody,.ovsec>.ovrows,.ovsec>.ovcolors,.ovsec>.ovlist,.ovsec>.ovgrid{padding:8px 12px}
.ovrows{row-gap:5px;column-gap:14px}
.ov .ovbox,.pf .ovbox{padding:3px 8px;min-height:24px}.ovrow>.ovnum,.ovrow>.pill,.ovrow>.chip,.ovrow>.tg{padding:3px 8px;min-height:24px}
.ovtr{padding:4px 8px}.ovcard{padding:8px 12px;margin-bottom:8px}.ovcard .ovbody>*+*{margin-top:8px}
.ovsec{margin-bottom:8px}
.ovsec>.ovsh,.pfo>.pfoh,.pfc>.pfch{background:var(--hdr);padding:5px 12px 5px 14px;font-weight:500;font-size:inherit;letter-spacing:0;text-transform:none;color:var(--fg);margin:0}
.ovsec>.ovsh .ovst,.pfc>.pfch{font-size:inherit;letter-spacing:0;text-transform:none;color:var(--fg)!important;font-weight:500}
.pfo>.pfoh b{font-weight:600}
details.ovfold>summary::before{content:none!important}
details.ovfold>summary::after{content:'▸';margin-left:8px;color:var(--mut);font-size:11px}details.ovfold[open]>summary::after{content:'▾'}
details.ovfold>summary{display:flex;align-items:center}
.pfob{padding:8px 12px}.pfob>*+*{margin-top:8px}.pf .ovbody>*+*{margin-top:6px}.pfkids{margin:8px 0 2px 8px;padding-left:10px}
.pfc{padding:0 0 4px 0}
.v-flag.bt{color:var(--num)}.v-flag.bf{color:var(--bool)}.v-flag{box-shadow:inset 3px 0 color-mix(in srgb,var(--bool) 45%,transparent)}
.ovrow>.ovbool{display:block}.pf .pfc>.ovbody,.pf .pfob>.ovbody{padding:6px 14px}.ovsh .tg,.pfoh .tg{margin-left:6px}
#main,#main>.ptitle,#main #top{background:var(--pane)}
.pfo{background:transparent}
.ovsec>.ovsh,.pfo>.pfoh,.pfc>.pfch,.ovsec>.ovsh .ovst,.pfc>.pfch,.pfo>.pfoh b{color:#f1f3f6!important}
.ovsh .tg,.pfoh .tg,.pfoh .pill{color:#aab2c0}
details.ovfold>summary::after{color:#aab2c0}
.pfoh .pill.off{background:transparent;color:#ff9a92}
.ovsec>.ovsh,.pfo>.pfoh,.pfc>.pfch{margin-left:-16px}
.ovsec>.ovsh,.pfo>.pfoh,.pfc>.pfch{padding-left:10px;margin-left:-12px}
.ovsec>.ovsh,.pfo>.pfoh,.pfc>.pfch{padding-left:12px;margin-left:-12px}
.ovsec>.ovbody,.ovsec>.ovtextbody,.ovsec>.ovrows,.ovsec>.ovcolors,.ovsec>.ovlist,.ovsec>.ovgrid,.ovsec>.ovtable,.pfob,.pf .pfc>.ovbody,.pf .pfob>.ovbody{padding-left:0;padding-right:0}
.ovsec>.ovtable{margin-left:0;margin-right:0}
.ovcard{padding-left:0;padding-right:0}.pfkids{margin-left:0;padding-left:0;border-left:0}
.ovsec,.pfo,.pfc,.pfkids{border-left:0!important}
.ov .ovrows,.pf .ovrows{grid-template-columns:240px minmax(0,1fr)!important}
.ovsec .ovsec,.pfc .ovsec{margin-left:16px}
.ovlist,.ovsec>.ovlist{padding-left:0;padding-right:0}
.ov .ovgrid{gap:6px;justify-content:flex-start;align-items:center}
.ov .ovgrid .chip{width:auto;max-width:100%;flex-direction:row;padding:3px 8px;min-height:24px;text-align:left;font-size:12.5px;background:var(--box)}
.ov .ovgrid .chip img.ico{height:30px;margin:0 6px 0 0}.ov .ovgrid .chip .sw{width:22px!important;height:22px!important;margin:0 6px 0 0!important}
.ovlistblock,.ovplainlist,.ovkv,.ovkvrow{margin-left:0;padding-left:0}
.ovcardhead{margin-left:0}
.ovkvrow{display:block!important;padding:8px 0}
.ovkvrow .ovkeycell{display:block;margin-bottom:6px}.ovkvrow .ovkeycell .ovbox{display:inline-block;min-width:240px}
.ovkv{padding-left:16px!important}.ovkv .tg{margin-bottom:4px}
.ovsec>.ovbody,.ovsec>.ovtextbody,.ovsec>.ovrows,.ovsec>.ovcolors,.ovsec>.ovlist,.ovsec>.ovgrid,.ovsec>.ovtable,.pfob,.pf .pfc>.ovbody,.pf .pfob>.ovbody{padding-left:16px!important}
.ovsec .ovsec,.pfc .ovsec{margin-left:0}
.ovlist,.ovsec>.ovlist{padding-left:0!important}.ovsec>.ovlist{padding-left:16px!important}
.ovkv{padding-left:0!important}.ovkv .tg{margin-left:0}
.pfob>.pfc,.pfob>.pfkids,.pfkids>.pfo{margin-left:0!important}
.pfroot>.pfob{padding-left:0!important}.pfroot>.pfrooti{padding:4px 0}.pfroot{background:transparent}
.pfsub{font-size:11px;letter-spacing:.07em;text-transform:uppercase;color:var(--mut);padding:10px 0 2px}.pfsub.kids{color:#5fb3b3}
.pfo.ovfold>.pfoh{background:color-mix(in srgb,var(--hdr) 62%,#1f9a9a)}
.pill.kid,.pf .pill.kid{background:transparent!important;color:#9fe0e0!important;border:1px solid #9fe0e055;font-size:10.5px;margin-left:10px;padding:0 6px}
.pfkids{border-left:0}
.pfdec{margin:22px 0 8px;padding-top:14px;border-top:1px solid var(--line);font-size:12px;letter-spacing:.06em;text-transform:uppercase;color:var(--mut)}
.pfann{color:var(--mut);margin-left:8px}

.uvbtn{position:absolute;left:10px;bottom:10px;border:1px solid #ffffff40;border-radius:7px;background:#14161acc;color:#d8dde4;padding:4px 11px;cursor:pointer;font:inherit;font-size:12.5px}.uvbtn:hover{background:#ffffff1f}.uvbtn.on{background:#3b6fd4;border-color:#6aa5ff;color:#fff}
.uvbox{position:absolute;left:10px;top:50px;border:1px solid #ffffff40;border-radius:7px;background:#14161ae6;padding:6px;color:#d8dde4;font-size:11.5px;line-height:1.3}.uvbox[hidden]{display:none}.uvbox canvas{display:block}.uvbox .uvcap{margin-top:4px;color:#9aa3ad}
</style></head><body>
<div id="app"><h1>Foundation Package Browser</h1><div class="sub" id="appsub"></div><span id="idx" title="Links between files are indexed in the background"></span></div>
<div id="cols"><div id="side"><div class="ptitle">Files</div><header><input id="q" placeholder="Search file names (all packages)…" autocomplete="off"></header>
<div id="fwrap"><div id="tbar"><label id="hm" title="Hide the .meta files that sit next to each asset"><input type="checkbox" id="hmcb"> Hide .meta files</label><span class="tbtns"><button class="btn" id="expl" title="Open every folder that is showing, one level deeper">＋ Level</button><button class="btn" id="coll" title="Close the deepest open folders, one level up">－ Level</button></span></div><button id="fbtn" class="btn" title="Show only folders and files of chosen types">Filter by type ▾</button><div id="fpanel" hidden></div></div>
<div id="results" hidden></div><div id="tree"></div></div>
<div id="main"><div class="ptitle">Inspector</div><div id="top"><button id="back" hidden title="Go back to the previous file">← Back</button><div><div id="title">Pick a file on the left</div><div id="meta"></div></div><label id="sg" title="Show raw GUIDs instead of the names of the files they point to"><input type="checkbox" id="sgcb"> Show GUIDs</label><label id="st" title="Show the data type (bool, string, float, …) after each value in the Overview"><input type="checkbox" id="stcb"> Show types</label></div>
<div id="tabs"></div><div id="body"><div class="note">Browse the folders or use the search box.</div></div></div></div>
<script>
const $=s=>document.querySelector(s);
function el(t,c,x){const e=document.createElement(t);if(c)e.className=c;if(x!==undefined)e.textContent=x;return e}
async function api(p,params){const r=await fetch('/api/'+p+'?'+new URLSearchParams(params||{}));const j=await r.json();if(!r.ok)throw new Error(j.error||r.status);return j}
function fmt(n){if(n<1024)return n+' B';const u=['KB','MB','GB'];let i=-1;do{n/=1024;i++}while(n>=1024&&i<2);return n.toFixed(n<10?1:0)+' '+u[i]}
const rawUrl=(pkg,path)=>'/api/raw?'+new URLSearchParams({pkg,path});
let selRow=null,cur=null,hist=[],dirNodes={},guidSpans=[],linkNote='';
function selectRow(r){if(selRow)selRow.classList.remove('sel');selRow=r;if(r)r.classList.add('sel')}
function fileRow(pkg,path,name,size){const r=el('div','row',name);r.title=path;r.dataset.path=path;r.append(el('span','sz',fmt(size)));r.onclick=()=>{selectRow(r);openFile(pkg,path)};return r}
let filt=new Set();let hideMeta=true;try{hideMeta=localStorage.getItem('hideMeta')!=='0'}catch(e){}
const extP=()=>Object.assign(filt.size?{ext:[...filt].join(',')}:{},hideMeta?{nometa:1}:{});
async function fill(ul,pkg,path){const r=await api('ls',Object.assign({pkg,path},extP()));
 for(const d of r.dirs)ul.append(dirItem(pkg,path?path+'/'+d:d,d));
 for(const f of r.files){const li=el('li');li.append(fileRow(pkg,path?path+'/'+f.name:f.name,f.name,f.size));ul.append(li)}}
let openDirs=new Set();try{openDirs=new Set(JSON.parse(localStorage.getItem('openDirs')||'[]'))}catch(e){}
const saveOpen=()=>{try{localStorage.setItem('openDirs',JSON.stringify([...openDirs]))}catch(e){}};
const parentKey=k=>{const c=k.indexOf(':'),i=k.lastIndexOf('/');return i>c?k.slice(0,i):(k.length>c+1?k.slice(0,c+1):null)};
function dirItem(pkg,path,name,extra){const li=el('li');const row=el('div','row dir');const ar=el('span','','▸ ');row.append(ar,document.createTextNode(name));
 if(extra)row.append(el('span','sz',extra));li.append(row);const ul=el('ul');ul.hidden=true;li.append(ul);let loaded=false;
 const key=pkg+':'+path;
 const node={ul,row,isOpen:false,async open(){if(!loaded){loaded=true;try{await fill(ul,pkg,path)}catch(e){ul.append(el('li','note',String(e.message)))}}ul.hidden=false;ar.textContent='▾ ';node.isOpen=true;openDirs.add(key);saveOpen()},
  close(){ul.hidden=true;ar.textContent='▸ ';node.isOpen=false;openDirs.delete(key);saveOpen()}};
 dirNodes[key]=node;
 row.onclick=async()=>{if(!node.isOpen)await node.open();else node.close()};return li}
async function restoreOpen(){const keys=[...openDirs].sort((a,b)=>a.split('/').length-b.split('/').length);
 for(const k of keys){const n=dirNodes[k];if(n&&!n.isOpen)await n.open()}}
async function expandLevel(){const todo=Object.entries(dirNodes).filter(([k,n])=>{if(n.isOpen)return false;const pk=parentKey(k);return !pk||(dirNodes[pk]&&dirNodes[pk].isOpen)}).map(x=>x[1]);
 for(let i=0;i<todo.length;i+=16)await Promise.all(todo.slice(i,i+16).map(n=>n.open()))}
function collapseLevel(){const ents=Object.entries(dirNodes).filter(([k,n])=>n.isOpen);
 const hasOpenKid=new Set();for(const [k] of ents){const pk=parentKey(k);if(pk)hasOpenKid.add(pk)}
 for(const [k,n] of ents)if(!hasOpenKid.has(k))n.close()}
async function reveal(pkg,path){if(!$('#results').hidden)return;const parts=path.split('/');let key=pkg+':';
 for(let i=0;i<=parts.length-1;i++){const n=dirNodes[key];if(!n)return;await n.open();if(i===parts.length-1){const ul=n.ul;
   for(const li of ul.children){const r=li.firstChild;if(r&&r.dataset&&r.dataset.path===path){selectRow(r);r.scrollIntoView({block:'center'});return}}return}
  key=key+(key.endsWith(':')?'':'/')+parts[i]}}
function setNote(t){linkNote=t;const m=$('#meta');m.textContent=(cur?cur.base:'')+(t?' · '+t:'')}
function appendFields(host,fields){
 if(!fields.length)return;
 if(fields.length===1){host.append(document.createTextNode(' = '));host.append(valueEl(fields[0]));return}
 host.append(document.createTextNode(' = { '));
 fields.forEach((f,i)=>{if(i)host.append(document.createTextNode(', '));host.append(el('span','tg',f.tag+'='));host.append(valueEl(f))});
 host.append(document.createTextNode(' }'))}
let showGuids=false;
const baseOf=p=>p.split('/').pop();
function hitName(hit){return hit.sub&&hit.name?hit.name+' in '+baseOf(hit.path):baseOf(hit.path)}
function applyGuidText(s){const t=[...s.childNodes].find(n=>n.nodeType===3);if(!t)return;if(s.dataset.orig===undefined)s.dataset.orig=t.nodeValue;
 t.nodeValue=(!showGuids&&s.dataset.nm)?s.dataset.nm:(showGuids?s.dataset.guid:s.dataset.orig)}
function swatch(c){const w=el('span','sw');w.style.cssText='display:inline-block;width:12px;height:12px;border-radius:3px;margin:0 5px -1px 0;border:1px solid #0006;background:rgb('+c.map(v=>Math.round(v*255))+')';return w}
const ICON_EXT=['png','jpg','jpeg','gif','tga','tif','tiff','dds'];
function icon(hit){const e=hit.path.split('.').pop().toLowerCase();if(hit.sub||!ICON_EXT.includes(e))return null;
 const i=document.createElement('img');i.className='ico';i.loading='lazy';i.alt='';i.src=texUrl(hit);i.onerror=()=>i.remove();return i}
function decorate(s,hit){if(s.querySelector('.sw,.ico'))return;if(hit.color)s.prepend(swatch(hit.color));else{const i=icon(hit.icon||hit);if(i){if(hit.icon)i.title='first image used by this file: '+hit.icon.path.split('/').pop();s.prepend(i)}}}
function guidResolved(s,hit){s.dataset.nm=hitName(hit);applyGuidText(s);decorate(s,hit)}
function valueEl(f){const s=el('span','t-'+f.type,String(f.value));
 if(f.type==='guid'&&f.value!=='00000000-0000-0000-0000-000000000000'){s.dataset.guid=f.value;s.title='GUID (click to copy)';s.classList.add('nolink');
  s.onclick=()=>{try{navigator.clipboard.writeText(f.value)}catch(e){}};guidSpans.push(s);scheduleResolve()}
 s.append(el('span','ty',f.type));return s}
let resolveTimer=null,resolveGen=0,pollTimer=null;
function scheduleResolve(){clearTimeout(resolveTimer);resolveTimer=setTimeout(resolveGuids,80)}
async function resolveGuids(){const gen=resolveGen;const spans=guidSpans.filter(s=>!s.dataset.done);if(!spans.length)return;
 const ids=[...new Set(spans.map(s=>s.dataset.guid))].slice(0,400);
 let r;try{r=await api('guids',{ids:ids.join(',')})}catch(e){return}
 if(gen!==resolveGen)return;
 for(const s of spans){const hit=r.found[s.dataset.guid];
  if(hit){s.dataset.done=1;guidResolved(s,hit);s.classList.remove('nolink');s.classList.add('link');s.title=s.dataset.guid+'\n'+(hit.sub?'part of ':'')+hit.pkg+' / '+hit.path+(hit.type?'  ['+hit.type+']':'');s.onclick=()=>follow(hit.pkg,hit.path,hit.sub?s.dataset.guid:null)}
  else if(r.finished&&ids.includes(s.dataset.guid)){s.dataset.done=1;s.title='GUID not found in the loaded packages (click to copy)'}}
 if(!r.finished){setNote('indexing links… '+r.done+' / '+r.total);clearTimeout(pollTimer);pollTimer=setTimeout(resolveGuids,1200)}else setNote('')}
async function follow(pkg,path,focus){await openFile(pkg,path,false,focus);reveal(pkg,path)}
function nodeEl(pkg,path,n,depth){
 if(n.child){const d=document.createElement('details');const s=document.createElement('summary');s.append(el('span','nm',n.name));appendFields(s,n.fields);d.append(s);
  const body=el('div');d.append(body);let loaded=false;
  const load=async()=>{if(loaded)return;loaded=true;try{await loadNodes(body,pkg,path,n.child,0,depth+1)}catch(e){body.append(el('div','note',String(e.message)))}};
  d.addEventListener('toggle',()=>{if(d.open)load()});if(depth<2){d.open=true;load()}return d}
 const l=el('div','leaf');l.append(el('span','nm',n.name));appendFields(l,n.fields);return l}
async function loadNodes(host,pkg,path,at,skip,depth){const r=await api('nodes',{pkg,path,at,skip});
 for(const n of r.items)host.append(nodeEl(pkg,path,n,depth));
 if(r.next!==null){const b=el('button','btn','Show more…');b.onclick=async()=>{b.remove();await loadNodes(host,pkg,path,at,r.next,depth)};host.append(b)}}
function setTabs(tabs,extraLinks){const t=$('#tabs');t.textContent='';let first=null;
 for(const [name,fn] of tabs){const b=el('button','',name);b.onclick=async()=>{for(const x of t.querySelectorAll('button'))x.classList.remove('on');b.classList.add('on');const body=$('#body');body.textContent='';guidSpans=[];resolveGen++;try{await fn(body)}catch(e){body.append(el('div','note',String(e.message)))}};t.append(b);if(!first)first=b}
 let firstLink=true;for(const [label,href] of (extraLinks||[])){const a=el('a',firstLink?'first':'',label);a.href=href;t.append(a);firstLink=false}
 if(first)first.click()}
async function hexTab(body){const {pkg,path}=cur;const pre=el('pre');body.append(pre);const more=el('button','btn','Next 4 KB');
 async function load(off){const r=await api('hex',{pkg,path,offset:off});pre.textContent+=(pre.textContent?'\n':'')+r.hex;if(r.next!==null){more.onclick=()=>load(r.next);more.hidden=false}else more.hidden=true}
 body.append(el('div'),more);await load(0)}
/* ---- 3D model viewer (hand-written WebGL2, no libraries) ---- */
const M4={
 mul(a,b){const o=new Float32Array(16);for(let c=0;c<4;c++)for(let r=0;r<4;r++){let s=0;for(let k=0;k<4;k++)s+=a[k*4+r]*b[c*4+k];o[c*4+r]=s}return o},
 persp(fov,asp,n,f){const t=1/Math.tan(fov/2),o=new Float32Array(16);o[0]=t/asp;o[5]=t;o[10]=(f+n)/(n-f);o[11]=-1;o[14]=2*f*n/(n-f);return o},
 look(e,c,u){let z=[e[0]-c[0],e[1]-c[1],e[2]-c[2]];let l=Math.hypot(...z);z=z.map(v=>v/l);
  let x=[u[1]*z[2]-u[2]*z[1],u[2]*z[0]-u[0]*z[2],u[0]*z[1]-u[1]*z[0]];l=Math.hypot(...x);x=x.map(v=>v/l);
  const y=[z[1]*x[2]-z[2]*x[1],z[2]*x[0]-z[0]*x[2],z[0]*x[1]-z[1]*x[0]];
  return new Float32Array([x[0],y[0],z[0],0,x[1],y[1],z[1],0,x[2],y[2],z[2],0,-(x[0]*e[0]+x[1]*e[1]+x[2]*e[2]),-(y[0]*e[0]+y[1]*e[1]+y[2]*e[2]),-(z[0]*e[0]+z[1]*e[1]+z[2]*e[2]),1])}
};
const VS='#version 300 es\nlayout(location=0) in vec3 p;layout(location=1) in vec3 n;layout(location=2) in vec2 uv;\nuniform mat4 mvp;uniform mat4 view;uniform mat4 model;out vec3 vN;out vec2 vUV;\nvoid main(){vN=mat3(view)*(mat3(model)*n);vUV=uv;gl_Position=mvp*(model*vec4(p,1.0));}';
const FS='#version 300 es\nprecision mediump float;in vec3 vN;in vec2 vUV;uniform sampler2D tex;uniform vec4 col;uniform float useTex;uniform vec4 flatc;uniform float lit;out vec4 o;\nvoid main(){if(flatc.a>0.0){o=flatc;return;}vec4 b=useTex>0.5?texture(tex,vUV)*vec4(col.rgb,1.0):col;if(b.a<0.35)discard;\nvec3 n=normalize(vN);if(!gl_FrontFacing)n=-n;float l=0.42+0.62*max(dot(n,normalize(vec3(0.55,0.65,0.55))),0.0)+0.2*max(dot(n,normalize(vec3(-0.6,-0.2,0.3))),0.0);o=vec4(lit>0.5?b.rgb*l:b.rgb,1.0);}';
function hsl(h,s,l){const a=s*Math.min(l,1-l),f=n=>{const k=(n+h/30)%12;return l-a*Math.max(-1,Math.min(k-3,9-k,1))};return [f(0),f(8),f(4),1]}

function seg(labels,titles){const o={selectedIndex:0,onchange:null,el:el('div','seg')};
 const bs=labels.map((t,i)=>{const b=el('button',i?'':'on',t);if(titles)b.title=titles[i];b.onclick=()=>{o.selectedIndex=i;bs.forEach((x,k)=>x.classList.toggle('on',k===i));if(o.onchange)o.onchange()};o.el.append(b);return b});
 Object.defineProperty(o,'value',{get(){return labels[o.selectedIndex]}});return o}
const NATIVE_IMG=['png','jpg','jpeg','gif'];
function texUrl(t){const ext=t.path.split('.').pop().toLowerCase();return NATIVE_IMG.includes(ext)?rawUrl(t.pkg,t.path):'/api/png?'+new URLSearchParams({pkg:t.pkg,path:t.path})}
async function modelTab(body){
 const {pkg,path}=cur;const m=await api('model',{pkg,path});
 const wrap=el('div','mv'),left=el('div','mvc'),panel=el('div','mvp');wrap.append(left,panel);body.append(wrap);
 for(const [suf,p] of Object.entries(m.related||{})){const b=el('button','btn','Open '+suf);b.onclick=()=>follow(pkg,p);panel.append(b)}
 if(!m.links_ready)left.append(el('div','note','Still indexing links between files. Materials and textures may be incomplete. Reopen this model in a moment.'));
 if(!m.has_geometry){left.append(el('div','note','The geometry file (' + path.split('/').pop() + '.data-xbin.meta) is not in this package, so only the model description is shown.'))}
 const canvas=el('canvas');const cw=el('div','cv');cw.append(canvas);left.append(cw);if(!m.has_geometry)cw.hidden=true;
 const info=el('div','note','');left.append(info);
 const lods=[...new Set(m.meshes.map(x=>x.lod))].sort((a,b)=>a-b);
 let lod=lods[0],showTex=true,wire=false,place=true;const hid=new Set(m.meshes.map((x,i)=>x.collider?i:-1).filter(i=>i>=0));
 const ctl=el('div','mvctl');panel.append(ctl);
 const sel=el('select');for(const l of lods){const o=el('option','','LOD '+l+' ('+m.meshes.filter(x=>x.lod===l).length+' meshes)');o.value=l;sel.append(o)}
 ctl.append(el('label','','Detail level '),sel);
 const cbT=el('input');cbT.type='checkbox';cbT.checked=true;const lT=el('label','');lT.append(cbT,document.createTextNode(' Textures'));
 const cbW=el('input');cbW.type='checkbox';const lW=el('label','');lW.append(cbW,document.createTextNode(' Wireframe'));
 const litSel=seg(['Lit','Unlit'],['Lit from the top right','Unlit: plain colours and textures, no shading']);
 const tbar=el('div','cvbar');tbar.append(litSel.el);cw.append(tbar);
 ctl.append(el('br'),lT,document.createTextNode('   '),lW);
 const cbP=el('input');cbP.type='checkbox';cbP.checked=true;
 if(m.meshes.some(x=>x.xf)){const lP=el('label','');lP.append(cbP,document.createTextNode(' Place parts as in the scene'));lP.title='Untick to draw every part at the model origin';ctl.append(el('br'),lP);
  cbP.onchange=()=>{place=cbP.checked;fit();dirty=true}}
 let groupRefresh=()=>{},setOpen=()=>{},cbColl=null;
 const nTop=m.groups.length;
 panel.append(el('h4','','Meshes'));
 const bar=el('div','mvbar');const mkBtn=(label,fn)=>{const b=el('button','btn',label);b.onclick=fn;bar.append(b)};
 mkBtn('Show all',()=>{m.meshes.forEach((x,i)=>{if(!x.collider||(cbColl&&cbColl.checked))hid.delete(i)});groupRefresh();dirty=true});
 mkBtn('Hide all',()=>{m.meshes.forEach((x,i)=>hid.add(i));groupRefresh();dirty=true});
 mkBtn('Fit view',()=>{fit();dirty=true});
 if(nTop){mkBtn('Expand all',()=>setOpen(true));mkBtn('Collapse all',()=>setOpen(false))}
 panel.append(bar);
 if(m.meshes.some(x=>x.collider)){cbColl=el('input');cbColl.type='checkbox';const l=el('label','');l.append(cbColl,document.createTextNode(' Show collision shapes'));
  cbColl.onchange=()=>{m.meshes.forEach((x,i)=>{if(x.collider)cbColl.checked?hid.delete(i):hid.add(i)});groupRefresh();dirty=true};panel.append(l)}
 const list=el('div','mvlist mvtree');panel.append(list);
 if(nTop>1)left.append(el('div','note','This file holds '+nTop+' separate objects drawn on top of each other. Use the tick boxes in the Meshes tree to show them one at a time (the "only" links are quickest).'));
 const mats=el('div','mvlist');panel.append(el('h4','','Materials'),mats);
 m.materials.forEach((x,i)=>{const r=el('div','mrow');const sw=el('span','sw');const c=hsl((i*67)%360,0.55,0.55);sw.style.background='rgb('+c.slice(0,3).map(v=>Math.round(v*255))+')';r.append(sw);if(x.material){const a=el('span','link',i+': '+x.name);a.title='Open material file';a.onclick=()=>follow(x.material.pkg,x.material.path);r.append(a,document.createTextNode(' '))}else r.append(document.createTextNode(i+': '+x.name+' '));
  if(x.texture){const a=el('span','link',x.texture.path.split('/').pop());a.onclick=()=>follow(x.texture.pkg,x.texture.path);a.title=x.texture.pkg+' / '+x.texture.path;r.append(a)}
  else if(x.tex)r.append(el('span','tg',x.tex+' (not found)'));mats.append(r)});
 if(!m.materials.length)mats.append(el('div','note','No material table found.'));
 if(!m.has_geometry){const t=el('table','mt');t.append(Object.assign(el('tr'),{innerHTML:'<th>Mesh</th><th>Mat</th><th>Verts</th><th>Tris</th><th>LOD</th>'}));
  for(const x of m.meshes){const r=el('tr');for(const v of [x.name,x.slot,x.verts,x.tris,x.lod])r.append(el('td','',v));t.append(r)}left.append(t);return}
 const gl=canvas.getContext('webgl2',{antialias:true});
 if(!gl){left.append(el('div','note','Your browser does not offer WebGL2, so the 3D view cannot be shown.'));return}
 const sh=(t,s)=>{const o=gl.createShader(t);gl.shaderSource(o,s);gl.compileShader(o);if(!gl.getShaderParameter(o,gl.COMPILE_STATUS))throw new Error(gl.getShaderInfoLog(o));return o};
 const prog=gl.createProgram();gl.attachShader(prog,sh(gl.VERTEX_SHADER,VS));gl.attachShader(prog,sh(gl.FRAGMENT_SHADER,FS));gl.linkProgram(prog);
 if(!gl.getProgramParameter(prog,gl.LINK_STATUS))throw new Error(gl.getProgramInfoLog(prog));
 const U=n=>gl.getUniformLocation(prog,n);const uLit=U('lit'),uMvp=U('mvp'),uView=U('view'),uTex=U('tex'),uCol=U('col'),uUse=U('useTex'),uFlat=U('flatc'),uModel=U('model');
 const cache={},texs={};let cam={yaw:0.6,pitch:0.35,dist:5,tx:0,ty:0,tz:0,r:1},dirty=true,dead=false,loading=0;
 const matCol=i=>hsl((i*67)%360,0.55,0.55);
 function getTex(slot){if(slot in texs)return texs[slot];const mt=m.materials[slot];texs[slot]=null;
  if(!mt||!mt.texture)return null;const img=new Image();img.onerror=()=>{texs[slot]=null};img.onload=()=>{const t=gl.createTexture();gl.bindTexture(gl.TEXTURE_2D,t);
   gl.texImage2D(gl.TEXTURE_2D,0,gl.RGBA,gl.RGBA,gl.UNSIGNED_BYTE,img);gl.generateMipmap(gl.TEXTURE_2D);
   gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MIN_FILTER,gl.LINEAR_MIPMAP_LINEAR);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_WRAP_S,gl.REPEAT);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_WRAP_T,gl.REPEAT);
   texs[slot]=t;dirty=true};img.src=texUrl(mt.texture);return null}
 async function load(i){if(cache[i])return cache[i];
  const r=await fetch('/api/mesh?'+new URLSearchParams({pkg,path,i}));if(!r.ok)throw new Error('could not load mesh '+i);
  const buf=await r.arrayBuffer();const dv=new DataView(buf);const nv=dv.getUint32(0,true),ni=dv.getUint32(4,true);
  const f=new Float32Array(buf,8,nv*15),idx=new Uint32Array(buf,8+nv*60,ni);
  const vao=gl.createVertexArray();gl.bindVertexArray(vao);const vb=gl.createBuffer();gl.bindBuffer(gl.ARRAY_BUFFER,vb);gl.bufferData(gl.ARRAY_BUFFER,new Uint8Array(buf,8,nv*60),gl.STATIC_DRAW);
  gl.enableVertexAttribArray(0);gl.vertexAttribPointer(0,3,gl.FLOAT,false,60,0);
  gl.enableVertexAttribArray(1);gl.vertexAttribPointer(1,3,gl.FLOAT,false,60,12);
  gl.enableVertexAttribArray(2);gl.vertexAttribPointer(2,2,gl.FLOAT,false,60,48);
  const ib=gl.createBuffer();gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER,ib);gl.bufferData(gl.ELEMENT_ARRAY_BUFFER,idx,gl.STATIC_DRAW);
  const lo=[1e30,1e30,1e30],hi=[-1e30,-1e30,-1e30];for(let k=0;k<nv;k++)for(let a=0;a<3;a++){const v=f[k*15+a];if(v<lo[a])lo[a]=v;if(v>hi[a])hi[a]=v}
  const e=new Uint32Array(ni*2);for(let t=0;t<ni;t+=3){const a=idx[t],b=idx[t+1],c=idx[t+2];e.set([a,b,b,c,c,a],t*2)}
  const vaoW=gl.createVertexArray();gl.bindVertexArray(vaoW);gl.bindBuffer(gl.ARRAY_BUFFER,vb);
  gl.enableVertexAttribArray(0);gl.vertexAttribPointer(0,3,gl.FLOAT,false,60,0);gl.disableVertexAttribArray(1);gl.disableVertexAttribArray(2);
  const eb=gl.createBuffer();gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER,eb);gl.bufferData(gl.ELEMENT_ARRAY_BUFFER,e,gl.STATIC_DRAW);
  gl.bindVertexArray(null);return cache[i]={vao,vaoW,ni,ne:e.length,lo,hi,f,idx}}
 const IDENT=new Float32Array([1,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1]);
 const mdl=x=>place&&x.xf?x.xf:IDENT;
 function fit(){let lo=[1e30,1e30,1e30],hi=[-1e30,-1e30,-1e30],any=false;
  m.meshes.forEach((x,i)=>{if(x.lod===lod&&!hid.has(i)&&cache[i]){any=true;const w=mdl(x),c=cache[i];
   for(let k=0;k<8;k++){const v=[k&1?c.hi[0]:c.lo[0],k&2?c.hi[1]:c.lo[1],k&4?c.hi[2]:c.lo[2]];
    for(let a=0;a<3;a++){const t=v[0]*w[a]+v[1]*w[4+a]+v[2]*w[8+a]+w[12+a];lo[a]=Math.min(lo[a],t);hi[a]=Math.max(hi[a],t)}}}});
  if(!any)return;cam.tx=(lo[0]+hi[0])/2;cam.ty=(lo[1]+hi[1])/2;cam.tz=(lo[2]+hi[2])/2;
  cam.r=Math.max(Math.hypot(hi[0]-lo[0],hi[1]-lo[1],hi[2]-lo[2])/2,1e-3);cam.dist=cam.r*2.4}
 async function setLod(l){lod=l;let tv=0,tt=0;
  m.meshes.forEach(x=>{if(x.lod===l&&!x.collider){tv+=x.verts;tt+=x.tris}});buildTree();
  info.textContent='Loading… ';loading++;
  try{await Promise.all(m.meshes.map((x,i)=>x.lod===l?load(i):null))}catch(e){info.textContent=e.message;loading--;return}
  loading--;if(lod!==l)return;info.textContent=tv.toLocaleString()+' vertices · '+tt.toLocaleString()+' triangles · drag to rotate, right-drag or Shift-drag to pan, wheel to zoom';fit();dirty=true}
 const openState=new Map();let groupUpd=[];
 function flat(g){let label=g.name;while(!g.direct.length&&g.children.length===1){const c=g.children[0];if(c.name+'_Part'!==label)label+=' › '+c.name;g=c}return [label,g]}
 function meshRow(host,i,depth,prefix){const x=m.meshes[i];const r=el('label','mrow');r.style.paddingLeft=(depth*14+4)+'px';
  const cb=el('input');cb.type='checkbox';cb.checked=!hid.has(i);cb.dataset.mesh=i;cb.onchange=()=>{cb.checked?hid.delete(i):hid.add(i);groupRefresh();dirty=true};
  const sw=el('span','sw');const c=matCol(x.slot);sw.style.background='rgb('+c.slice(0,3).map(v=>Math.round(v*255))+')';
  let nm=x.name;if(prefix&&nm.startsWith(prefix+'_'))nm=nm.slice(prefix.length+1);r.title=x.name;
  r.append(cb,sw,document.createTextNode(nm+' '),el('span','tg',(x.collider?'collision · ':'')+'mat '+x.slot+' · '+x.verts+' v · '+x.tris+' tris'));host.append(r)}
 function renderGroup(host,g0,depth,path){const [label,g]=flat(g0);
  const all=g.meshes.filter(i=>m.meshes[i].lod===lod);if(!all.length)return;
  const ms=g.meshes.filter(i=>!m.meshes[i].collider);const key=path+'/'+label;
  const d=document.createElement('details');d.open=openState.has(key)?openState.get(key):(depth>0||nTop<=3);d.addEventListener('toggle',()=>openState.set(key,d.open));d.dataset.key=key;
  const sm=document.createElement('summary');sm.style.marginLeft='0';sm.style.paddingLeft=(depth*14)+'px';
  const cb=el('input');cb.type='checkbox';cb.onclick=e=>e.stopPropagation();const ar=el('span','ar',d.open?'▾':'▸');d.addEventListener('toggle',()=>{ar.textContent=d.open?'▾':'▸'});
  const ct=el('span','tg','');const only=el('span','link','only');only.title='Show only this group';
  cb.onchange=()=>{for(const i of ms)cb.checked?hid.delete(i):hid.add(i);groupRefresh();dirty=true};
  only.onclick=e=>{e.preventDefault();e.stopPropagation();m.meshes.forEach((x,i)=>{if(!x.collider)hid.add(i)});for(const i of ms)hid.delete(i);groupRefresh();fit();dirty=true};
  const nmEl=el('span','nm',label);nmEl.title=label;sm.append(ar,cb,nmEl,ct,only);d.append(sm);
  const upd=()=>{const cur=all.filter(i=>!m.meshes[i].collider);const nv=cur.filter(i=>!hid.has(i)).length;cb.checked=nv>0&&nv===cur.length;cb.indeterminate=nv>0&&nv<cur.length;cb.disabled=!cur.length;ct.textContent=cur.length+' meshes'};
  groupUpd.push(upd);
  const body=el('div');d.append(body);for(const k of g.children)renderGroup(body,k,depth+1,key);
  for(const i of g.direct)if(m.meshes[i].lod===lod)meshRow(body,i,depth+1,g.name);
  host.append(d)}
 buildTree=()=>{list.textContent='';groupUpd=[];
  if(nTop){for(const g of m.groups)renderGroup(list,g,0,'')}
  else m.meshes.forEach((x,i)=>{if(x.lod===lod)meshRow(list,i,0,'')});groupRefresh()};
 groupRefresh=()=>{groupUpd.forEach(f=>f());list.querySelectorAll('input[data-mesh]').forEach(c=>{c.checked=!hid.has(+c.dataset.mesh)})};
 setOpen=on=>{list.querySelectorAll('details').forEach(d=>{d.open=on;openState.set(d.dataset.key,on)})};
 litSel.onchange=()=>{dirty=true};sel.onchange=()=>setLod(+sel.value);cbT.onchange=()=>{showTex=cbT.checked;dirty=true};cbW.onchange=()=>{wire=cbW.checked;dirty=true};
 let drag=null;canvas.oncontextmenu=e=>e.preventDefault();
 canvas.onpointerdown=e=>{canvas.setPointerCapture(e.pointerId);drag={x:e.clientX,y:e.clientY,pan:e.button!==0||e.shiftKey}};
 canvas.onpointerup=canvas.onpointercancel=()=>{drag=null};
 canvas.onpointermove=e=>{if(!drag)return;const dx=e.clientX-drag.x,dy=e.clientY-drag.y;drag.x=e.clientX;drag.y=e.clientY;
  if(drag.pan){const s=cam.dist*0.0016,cy=Math.cos(cam.yaw),sy=Math.sin(cam.yaw);cam.tx+=(-cy*dx)*s;cam.tz+=(sy*dx)*s;cam.ty+=dy*s}
  else{cam.yaw-=dx*0.008;cam.pitch=Math.max(-1.5,Math.min(1.5,cam.pitch+dy*0.008))}dirty=true};
 canvas.addEventListener('wheel',e=>{e.preventDefault();cam.dist=Math.max(cam.r*0.05,Math.min(cam.r*60,cam.dist*Math.exp(e.deltaY*0.0012)));dirty=true},{passive:false});
 function draw(){const dpr=window.devicePixelRatio||1,w=Math.max(1,Math.round(canvas.clientWidth*dpr)),h=Math.max(1,Math.round(canvas.clientHeight*dpr));
  if(canvas.width!==w||canvas.height!==h){canvas.width=w;canvas.height=h}
  gl.viewport(0,0,w,h);gl.clearColor(0.17,0.19,0.22,1);gl.clear(gl.COLOR_BUFFER_BIT|gl.DEPTH_BUFFER_BIT);gl.enable(gl.DEPTH_TEST);gl.useProgram(prog);
  const cp=Math.cos(cam.pitch),eye=[cam.tx+cam.dist*cp*Math.sin(cam.yaw),cam.ty+cam.dist*Math.sin(cam.pitch),cam.tz+cam.dist*cp*Math.cos(cam.yaw)];
  const view=M4.look(eye,[cam.tx,cam.ty,cam.tz],[0,1,0]),proj=M4.persp(0.8,w/h,cam.dist*0.01+cam.r*0.002,cam.dist+cam.r*40);
  gl.uniformMatrix4fv(uMvp,false,M4.mul(proj,view));gl.uniformMatrix4fv(uView,false,view);gl.uniform1i(uTex,0);gl.uniform1f(uLit,litSel.selectedIndex===0?1:0);
  gl.frontFace(gl.CW);let ff=true;gl.enable(gl.POLYGON_OFFSET_FILL);gl.polygonOffset(1,1);gl.uniform4f(uFlat,0,0,0,0);
  m.meshes.forEach((x,i)=>{if(x.lod!==lod||!!hid.has(i)||!cache[i])return;const c=cache[i],t=showTex?getTex(x.slot):null;
   gl.uniformMatrix4fv(uModel,false,mdl(x));const cw=!(place&&x.flip);if(cw!==ff){ff=cw;gl.frontFace(cw?gl.CW:gl.CCW)}
   if(t){gl.activeTexture(gl.TEXTURE0);gl.bindTexture(gl.TEXTURE_2D,t);gl.uniform1f(uUse,1);const tc=(m.materials[x.slot]||{}).color||[1,1,1,1];gl.uniform4f(uCol,Math.min(1,tc[0]),Math.min(1,tc[1]),Math.min(1,tc[2]),1)}else{gl.uniform1f(uUse,0);gl.uniform4fv(uCol,matCol(x.slot))}
   gl.bindVertexArray(c.vao);gl.drawElements(gl.TRIANGLES,c.ni,gl.UNSIGNED_INT,0)});
  if(wire){gl.disable(gl.POLYGON_OFFSET_FILL);gl.uniform4f(uFlat,0.05,0.05,0.07,1);
   m.meshes.forEach((x,i)=>{if(x.lod!==lod||!!hid.has(i)||!cache[i])return;gl.uniformMatrix4fv(uModel,false,mdl(x));gl.bindVertexArray(cache[i].vaoW);gl.drawElements(gl.LINES,cache[i].ne,gl.UNSIGNED_INT,0)})}
  gl.bindVertexArray(null);canvas.dataset.drawn=(+canvas.dataset.drawn||0)+1}
 // UV map overlay: UV edges of the ticked meshes, drawn on top of each other
 const uvBtn=el('button','uvbtn','UV map');uvBtn.title='Show the UV layout of the meshes that are ticked in the Meshes tree';
 const uvBox=el('div','uvbox');uvBox.hidden=true;const uvc=el('canvas');const uvCap=el('div','uvcap','');uvBox.append(uvc,uvCap);cw.append(uvBox,uvBtn);
 let uvOpen=false,uvKey='';
 function uvBounds(c){if(c.uvb)return c.uvb;const f=c.f,n=f.length/15;let u0=1e30,u1=-1e30,v0=1e30,v1=-1e30;
  for(let k=0;k<n;k++){const u=f[k*15+12],v=f[k*15+13];if(u<u0)u0=u;if(u>u1)u1=u;if(v<v0)v0=v;if(v>v1)v1=v}return c.uvb=[u0,u1,v0,v1]}
 function drawUV(){const vis=[];m.meshes.forEach((x,i)=>{if(x.lod===lod&&!hid.has(i)&&cache[i])vis.push(i)});
  const dpr=window.devicePixelRatio||1,S=Math.max(120,Math.min(300,Math.round(cw.clientWidth*0.42),Math.round(cw.clientHeight-110)));
  uvc.style.width=S+'px';uvc.style.height=S+'px';uvc.width=Math.round(S*dpr);uvc.height=Math.round(S*dpr);
  const g=uvc.getContext('2d');g.setTransform(dpr,0,0,dpr,0,0);g.fillStyle='#0d0f12';g.fillRect(0,0,S,S);
  let u0=0,u1=1,v0=0,v1=1;for(const i of vis){const b=uvBounds(cache[i]);if(isFinite(b[0])){u0=Math.min(u0,b[0]);u1=Math.max(u1,b[1]);v0=Math.min(v0,b[2]);v1=Math.max(v1,b[3])}}
  const span=Math.max(u1-u0,v1-v0,1e-6),pad=6,sc=(S-pad*2)/span,X=u=>pad+(u-u0)*sc,Y=v=>pad+(v-v0)*sc;
  g.lineWidth=1;g.strokeStyle='#ffffff18';g.beginPath();for(let a=Math.ceil(u0);a<=u1;a++){g.moveTo(X(a),pad);g.lineTo(X(a),S-pad)}for(let a=Math.ceil(v0);a<=v1;a++){g.moveTo(pad,Y(a));g.lineTo(S-pad,Y(a))}g.stroke();
  g.strokeStyle='#ffffff66';g.strokeRect(X(0),Y(0),sc,sc);
  let tris=0;g.lineWidth=1;
  for(const i of vis){const c=cache[i],f=c.f,ix=c.idx,col=matCol(m.meshes[i].slot);g.strokeStyle='rgba('+col.slice(0,3).map(v=>Math.round(v*255))+',0.7)';g.beginPath();
   for(let t=0;t+2<c.ni;t+=3){const a=ix[t]*15+12,b=ix[t+1]*15+12,d=ix[t+2]*15+12;
    g.moveTo(X(f[a]),Y(f[a+1]));g.lineTo(X(f[b]),Y(f[b+1]));g.lineTo(X(f[d]),Y(f[d+1]));g.closePath()}
   g.stroke();tris+=c.ni/3}
  uvCap.textContent=vis.length?vis.length+' mesh'+(vis.length>1?'es':'')+' · '+tris.toLocaleString()+' triangles · square = 0–1':'No meshes ticked'}
 function uvTick(){if(!uvOpen)return;const k=lod+':'+m.meshes.map((x,i)=>x.lod===lod&&!hid.has(i)&&cache[i]?i:'').join(',');if(k!==uvKey){uvKey=k;drawUV()}}
 uvBtn.onclick=()=>{uvOpen=!uvOpen;uvBtn.classList.toggle('on',uvOpen);uvBox.hidden=!uvOpen;uvKey='';uvTick()};
 (function loop(){if(dead||!canvas.isConnected)return;if(dirty){dirty=false;try{draw()}catch(e){info.textContent='Drawing failed: '+e.message}}uvTick();requestAnimationFrame(loop)})();
 window.__mv={cam,get lod(){return lod}};
 const fg=cur&&cur.focus;
 if(fg&&m.nodes&&m.nodes[fg]){const keep=new Set(m.nodes[fg]);m.meshes.forEach((x,i)=>{if(!keep.has(i))hid.add(i)});
  const nm=(m.nodes_named&&m.nodes_named[fg])||'the linked part';
  const fb=el('div','note','Showing only '+nm+' of this model. ');const al=el('span','link','Show whole model');
  al.onclick=()=>{m.meshes.forEach((x,i)=>{if(!x.collider||(cbColl&&cbColl.checked))hid.delete(i)});groupRefresh();fit();dirty=true;fb.remove()};fb.append(al);left.append(fb)}
 setLod(lod);
}


/* ---- material preview ---- */
async function materialTab(body){
 const {pkg,path}=cur;const m=await api('material',{pkg,path});
 const wrap=el('div','mv'),left=el('div','mvc'),panel=el('div','mvp');wrap.append(left,panel);body.append(wrap);
 const canvas=el('canvas');const cw=el('div','cv');cw.append(canvas);left.append(cw);
 const shapeSel=seg(['Sphere','Cube','Tile'],['Sphere','Cube','Flat tile (texture repeated twice)']),litM=seg(['Lit','Unlit'],['Lit from the top right','Unlit: plain colours and textures, no shading']);
 const tbar=el('div','cvbar');tbar.append(shapeSel.el,litM.el);cw.append(tbar);litM.onchange=()=>{dirty=true};
 if(!m.links_ready)left.append(el('div','note','Still indexing links between files; textures may appear in a moment. Reopen this file to refresh.'));
 const t=el('table','mt');const row=(k,v)=>{const r=el('tr');r.append(el('th','',k));const d=el('td');if(v instanceof Node)d.append(v);else d.textContent=v;r.append(d);t.append(r)};
 const sw=el('span','sw');sw.style.background='rgba('+m.color.slice(0,3).map(v=>Math.round(Math.min(1,v)*255))+','+m.color[3]+')';
 const cs=el('span','');cs.append(sw,document.createTextNode(m.color.map(v=>+v.toFixed(3)).join(', ')));row('Albedo colour',cs);
 row('Metalness',m.metalness??'');row('Roughness',m.roughness??'');row('Render mode',m.render_mode??'');row('Alpha test',String(m.alpha_test));row('Two-sided',String(m.two_sided));row('Casts shadow',String(m.shadow));
 panel.append(t,el('h4','','Textures'));
 const slots=Object.entries(m.textures);if(!slots.length)panel.append(el('div','note','No textures assigned.'));
 for(const [slot,tx] of slots){const d=el('div','texrow');d.append(el('div','tg',slot));
  if(tx.file){const a=el('span','link',tx.file.path.split('/').pop());a.onclick=()=>follow(tx.file.pkg,tx.file.path);d.append(a);const im=el('img','thumb');im.src=texUrl(tx.file);im.onerror=()=>{im.remove()};d.append(el('br'),im)}
  else d.append(el('span','tg','not found in the loaded packages ('+tx.guid+')'));panel.append(d)}
 const gl=canvas.getContext('webgl2',{antialias:true});if(!gl){left.append(el('div','note','WebGL2 is not available in this browser.'));return}
 const VSm='#version 300 es\nlayout(location=0) in vec3 p;layout(location=1) in vec3 n;layout(location=2) in vec2 uv;uniform mat4 mvp;uniform mat4 view;uniform float tile;out vec3 vN;out vec3 vP;out vec2 vUV;void main(){vN=mat3(view)*n;vP=(view*vec4(p,1.0)).xyz;vUV=uv*tile;gl_Position=mvp*vec4(p,1.0);}';
 const FSm='#version 300 es\nprecision mediump float;in vec3 vN;in vec3 vP;in vec2 vUV;uniform sampler2D tex;uniform vec4 col;uniform float useTex;uniform float rough;uniform float metal;uniform float lit;out vec4 o;void main(){vec4 b=useTex>0.5?texture(tex,vUV)*vec4(col.rgb,1.0):col;if(b.a<0.05)discard;vec3 n=normalize(vN);if(!gl_FrontFacing)n=-n;vec3 L=normalize(vec3(0.55,0.65,0.55));vec3 V=normalize(-vP);vec3 H=normalize(L+V);float d=max(dot(n,L),0.0);float sh=mix(200.0,8.0,clamp(rough,0.0,1.0));float sp=pow(max(dot(n,H),0.0),sh)*(1.0-rough*0.8);vec3 base=b.rgb*(1.0-metal*0.6);vec3 sc=mix(vec3(0.25),b.rgb,metal);o=vec4(lit>0.5?base*(0.4+0.8*d)+sc*sp:b.rgb,1.0);}';
 const sh=(ty,src)=>{const o=gl.createShader(ty);gl.shaderSource(o,src);gl.compileShader(o);if(!gl.getShaderParameter(o,gl.COMPILE_STATUS))throw new Error(gl.getShaderInfoLog(o));return o};
 const pr=gl.createProgram();gl.attachShader(pr,sh(gl.VERTEX_SHADER,VSm));gl.attachShader(pr,sh(gl.FRAGMENT_SHADER,FSm));gl.linkProgram(pr);
 const U=n=>gl.getUniformLocation(pr,n);
 function mk(verts,idx){const vao=gl.createVertexArray();gl.bindVertexArray(vao);const vb=gl.createBuffer();gl.bindBuffer(gl.ARRAY_BUFFER,vb);gl.bufferData(gl.ARRAY_BUFFER,new Float32Array(verts),gl.STATIC_DRAW);
  for(const [i,n,o] of [[0,3,0],[1,3,12],[2,2,24]]){gl.enableVertexAttribArray(i);gl.vertexAttribPointer(i,n,gl.FLOAT,false,32,o)}
  const ib=gl.createBuffer();gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER,ib);gl.bufferData(gl.ELEMENT_ARRAY_BUFFER,new Uint32Array(idx),gl.STATIC_DRAW);gl.bindVertexArray(null);return {vao,n:idx.length}}
 const sv=[],si=[],LA=40,LO=80;for(let a=0;a<=LA;a++){const th=a*Math.PI/LA;for(let o=0;o<=LO;o++){const ph=o*2*Math.PI/LO;const x=Math.sin(th)*Math.cos(ph),y=Math.cos(th),z=Math.sin(th)*Math.sin(ph);sv.push(x,y,z,x,y,z,o/LO*2,a/LA)}}
 for(let a=0;a<LA;a++)for(let o=0;o<LO;o++){const i=a*(LO+1)+o;si.push(i,i+1,i+LO+1,i+1,i+LO+2,i+LO+1)}
 const cv=[],ci=[];[[[0,0,1],[1,0,0],[0,1,0]],[[0,0,-1],[-1,0,0],[0,1,0]],[[1,0,0],[0,0,-1],[0,1,0]],[[-1,0,0],[0,0,1],[0,1,0]],[[0,1,0],[1,0,0],[0,0,-1]],[[0,-1,0],[1,0,0],[0,0,1]]].forEach(([n,u,v],k)=>{
  const b=cv.length/8;for(const [a,c] of [[-1,-1],[1,-1],[1,1],[-1,1]])cv.push(0.8*(n[0]+a*u[0]+c*v[0]),0.8*(n[1]+a*u[1]+c*v[1]),0.8*(n[2]+a*u[2]+c*v[2]),n[0],n[1],n[2],(a+1)/2,(c+1)/2);ci.push(b,b+1,b+2,b,b+2,b+3)});
 const cube=mk(cv,ci);
 const sphere=mk(sv,si),plane=mk([-1,-1,0,0,0,1,0,1,1,-1,0,0,0,1,1,1,1,1,0,0,0,1,1,0,-1,1,0,0,0,1,0,0],[0,1,2,0,2,3]);
 let tex=null,yaw=0.5,pitch=0.2,dirty=true;const url=m.textures.AlbedoTexture&&m.textures.AlbedoTexture.file;
 if(url){const im=new Image();im.onload=()=>{const t=gl.createTexture();gl.bindTexture(gl.TEXTURE_2D,t);gl.texImage2D(gl.TEXTURE_2D,0,gl.RGBA,gl.RGBA,gl.UNSIGNED_BYTE,im);gl.generateMipmap(gl.TEXTURE_2D);
  gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MIN_FILTER,gl.LINEAR_MIPMAP_LINEAR);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_WRAP_S,gl.REPEAT);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_WRAP_T,gl.REPEAT);tex=t;dirty=true};im.src=texUrl(url)}
 shapeSel.onchange=()=>{dirty=true};let drag=null;
 canvas.onpointerdown=e=>{canvas.setPointerCapture(e.pointerId);drag=[e.clientX,e.clientY]};canvas.onpointerup=canvas.onpointercancel=()=>{drag=null};
 canvas.onpointermove=e=>{if(!drag)return;yaw-=(e.clientX-drag[0])*0.01;pitch=Math.max(-1.5,Math.min(1.5,pitch+(e.clientY-drag[1])*0.01));drag=[e.clientX,e.clientY];dirty=true};
 function draw(){const dpr=window.devicePixelRatio||1,w=Math.max(1,Math.round(canvas.clientWidth*dpr)),h=Math.max(1,Math.round(canvas.clientHeight*dpr));if(canvas.width!==w||canvas.height!==h){canvas.width=w;canvas.height=h}
  gl.viewport(0,0,w,h);gl.clearColor(0.17,0.19,0.22,1);gl.clear(gl.COLOR_BUFFER_BIT|gl.DEPTH_BUFFER_BIT);gl.enable(gl.DEPTH_TEST);gl.useProgram(pr);
  const isPlane=shapeSel.value==='Tile',cp=Math.cos(pitch),d=isPlane?2.6:3.4,eye=isPlane?[0,0,d]:[d*cp*Math.sin(yaw),d*Math.sin(pitch),d*cp*Math.cos(yaw)];
  const view=M4.look(eye,[0,0,0],[0,1,0]);gl.uniformMatrix4fv(U('mvp'),false,M4.mul(M4.persp(0.8,w/h,0.1,50),view));gl.uniformMatrix4fv(U('view'),false,view);
  gl.uniform1f(U('tile'),isPlane?2:1);gl.uniform1f(U('lit'),litM.selectedIndex===0?1:0);gl.uniform1f(U('rough'),m.roughness??0.8);gl.uniform1f(U('metal'),m.metalness??0);gl.uniform1i(U('tex'),0);
  const c=m.color;if(tex){gl.bindTexture(gl.TEXTURE_2D,tex);gl.uniform1f(U('useTex'),1)}else gl.uniform1f(U('useTex'),0);gl.uniform4f(U('col'),c[0],c[1],c[2],1);
  const s=isPlane?plane:shapeSel.value==='Cube'?cube:sphere;gl.bindVertexArray(s.vao);gl.drawElements(gl.TRIANGLES,s.n,gl.UNSIGNED_INT,0);gl.bindVertexArray(null);canvas.dataset.drawn=(+canvas.dataset.drawn||0)+1}
 (function loop(){if(!canvas.isConnected)return;if(dirty){dirty=false;try{draw()}catch(e){left.append(el('div','note','Drawing failed: '+e.message))}}requestAnimationFrame(loop)})();
}


/* ---- prefab view ---- */
const ZERO_G='00000000-0000-0000-0000-000000000000';
const shortComp=t=>t.replace(/^[A-Za-z]{3}CComp/,'').replace(/^Comp/,'');
let chipSpans=[];
function baseName(p){return p.split('/').pop()}
function guidChip(g){const s=el('span','chip nolink',g.slice(0,8)+'…');s.dataset.guid=g;s.title=g+' (click to copy)';
 s.onclick=()=>{try{navigator.clipboard.writeText(g)}catch(e){}};chipSpans.push(s);return s}
async function resolveChips(tries){const spans=chipSpans.filter(s=>!s.dataset.done);if(!spans.length)return;
 const ids=[...new Set(spans.map(s=>s.dataset.guid))];let finished=true;
 for(let i=0;i<ids.length;i+=300){let r;try{r=await api('guids',{ids:ids.slice(i,i+300).join(',')})}catch(e){return}
  finished=finished&&r.finished;
  for(const s of spans){const hit=r.found[s.dataset.guid];if(!hit)continue;s.dataset.done=1;
   s.dataset.orig=s.textContent;s.dataset.nm=hitName(hit);applyGuidText(s);decorate(s,hit);s.classList.remove('nolink');s.classList.add('link');
   s.title=hit.pkg+' / '+hit.path+(hit.sub?'  (part of the file)':'')+(hit.type?'  ['+hit.type+']':'');s.onclick=()=>follow(hit.pkg,hit.path,hit.sub?s.dataset.guid:null)}}
 if(!finished&&tries<40)setTimeout(()=>resolveChips(tries+1),1500)
 else for(const s of spans)if(!s.dataset.done)s.title='GUID '+s.dataset.guid+' not found in the loaded packages (click to copy)'}
function fv(f){if(f.type==='guid')return f.value===ZERO_G?el('span','tg','none'):guidChip(f.value);
 const s=el('span','t-'+f.type,f.type==='bool'?String(f.value):String(f.value));return s}
function fieldLine(host,e,depth){
 const kids=e.c||[];const own=e.f||[];
 const leaf=k=>!(k.c&&k.c.length)&&k.f&&k.f.length===1;
 if(!kids.length||(kids.length<=4&&kids.every(leaf)&&!own.length)){
  const l=el('div','leaf');l.append(el('span','nm',e.n));
  if(kids.length){l.append(document.createTextNode(' = { '));kids.forEach((k,i)=>{if(i)l.append(document.createTextNode(', '));l.append(el('span','tg',k.n+'='),fv(k.f[0]))});l.append(document.createTextNode(' }'))}
  else if(own.length===1){l.append(document.createTextNode(' = '),fv(own[0]))}
  else if(own.length){l.append(document.createTextNode(' = { '));own.forEach((f,i)=>{if(i)l.append(document.createTextNode(', '));l.append(el('span','tg',f.tag+'='),fv(f))});l.append(document.createTextNode(' }'))}
  host.append(l);return}
 const d=document.createElement('details');const sm=document.createElement('summary');sm.append(el('span','nm',e.n+' '));
 if(own.length)own.forEach(f=>{sm.append(el('span','tg',(f.tag?f.tag+'=':'')),fv(f),document.createTextNode(' '))});
 sm.append(el('span','tg','('+kids.length+')'));d.append(sm);const b=el('div');d.append(b);let built=false;
 const build=()=>{if(built)return;built=true;kids.forEach(k=>fieldLine(b,k,depth+1))};
 d.addEventListener('toggle',()=>{if(d.open)build()});if(depth<1){d.open=true;build()}host.append(d)}
const near=(a,b)=>Math.abs(a-b)<1e-4;
function transformText(t){if(!t)return '';const parts=[];const f=v=>v.map(x=>+(+x).toFixed(3)).join(', ');
 if(!t.p.every(x=>near(x,0)))parts.push('position ('+f(t.p)+')');
 if(!(near(t.r[0],0)&&near(t.r[1],0)&&near(t.r[2],0)))parts.push('rotation ('+f(t.r)+')');
 if(!t.s.every(x=>near(x,1)))parts.push('scale ('+f(t.s)+')');return parts.join('  ·  ')}
function compSummary(c){const bits=[];const walk=(fs)=>fs;
 for(const k of (c.c||[])){if(k.f&&k.f.length===1&&k.f[0].type==='guid'&&k.f[0].value!==ZERO_G&&bits.length<3){bits.push([k.n,k.f[0].value])}}
 return bits}
function compEl(c){const d=document.createElement('details');d.className='comp';const sm=document.createElement('summary');
 const nm=el('span','nm',shortComp(c.type));nm.title=c.type;sm.append(nm);
 for(const [k,g] of compSummary(c)){sm.append(document.createTextNode('  '),el('span','tg',k+':'),guidChip(g))}
 d.append(sm);const b=el('div');d.append(b);let built=false;
 d.addEventListener('toggle',()=>{if(d.open&&!built){built=true;const n=(c.c||[]).length+(c.f||[]).length;if(!n)b.append(el('div','tg','(no fields)'));(c.c||[]).forEach(k=>fieldLine(b,k,1))}});return d}
function countObjs(o,acc){acc.objs++;for(const c of o.components)acc.comps[c.type]=(acc.comps[c.type]||0)+1;for(const k of o.children)countObjs(k,acc);return acc}
function collectGuids(o,acc){if(o.asset)acc.set(o.asset,(acc.get(o.asset)||0)+1);
 const walk=e=>{if(e.f)for(const f of e.f)if(f.type==='guid'&&f.value!==ZERO_G)acc.set(f.value,(acc.get(f.value)||0)+1);if(e.c)e.c.forEach(walk)};
 for(const c of o.components)walk(c);for(const k of o.children)collectGuids(k,acc)}
function objEl(o,depth){const d=document.createElement('details');d.className='obj';const sm=document.createElement('summary');
 const nm=el('span','nm',o.name||'(unnamed)');sm.append(nm);
 if(o.flags.isActive===false)sm.append(el('span','pill off','inactive'));
 const kinds=[...new Set(o.components.map(c=>shortComp(c.type)))];
 kinds.slice(0,5).forEach(k=>sm.append(el('span','pill',k)));if(kinds.length>5)sm.append(el('span','pill','+'+(kinds.length-5)));
 if(o.asset){sm.append(el('span','tg','  model part:'),guidChip(o.asset))}
 if(o.children.length)sm.append(el('span','tg','  '+o.children.length+' child'+(o.children.length>1?'ren':'')));
 d.append(sm);const b=el('div','objbody');d.append(b);let built=false;
 const build=()=>{if(built)return;built=true;const tx=transformText(o.transform);if(tx)b.append(el('div','tg',tx));
  const extra=Object.entries(o.flags).filter(([k,v])=>k!=='isActive'&&v!==undefined);
  if(extra.length||o.id){const m=el('div','tg');m.textContent=extra.map(([k,v])=>k+'='+v).join('  ')+(o.id?(extra.length?'  ':'')+'id '+o.id:'');b.append(m)}
  o.components.forEach(c=>b.append(compEl(c)));o.children.forEach(k=>b.append(objEl(k,depth+1)));resolveChips(0)};
 d.addEventListener('toggle',()=>{if(d.open)build()});if(depth<1){d.open=true;build()}return d}
function rawNodeEl(e,depth){
 const kids=e.c||[],own=e.f||[];
 if(!kids.length){const l=el('div','leaf');l.append(el('span','nm',e.n));appendFields(l,own);return l}
 const d=document.createElement('details');d.className='rawn';const s=document.createElement('summary');s.append(el('span','nm',e.n));appendFields(s,own);
 const ob=kids.find(k=>k.n==='object');
 if(ob){const nmf=(ob.c||[]).find(k=>k.n==='name');const comps=(((ob.c||[]).find(k=>k.n==='components')||{}).c||[]);
  if(nmf&&nmf.f&&nmf.f[0])s.append(el('span','pfann','  '+nmf.f[0].value));
  const ks=[...new Set(comps.map(c=>shortComp(c.n)))];ks.slice(0,5).forEach(k=>s.append(el('span','pill',k)));if(ks.length>5)s.append(el('span','pill','+'+(ks.length-5)))}
 d.append(s);const b=el('div');d.append(b);let built=false;
 const build=()=>{if(built)return;built=true;for(const k of kids)b.append(rawNodeEl(k,depth+1));resolveChips(0)};
 d.addEventListener('toggle',()=>{if(d.open)build()});if(depth<2){d.open=true;build()}return d}
async function prefabTab(body,opts){
 const {pkg,path}=cur;const p=await api('prefab',{pkg,path});chipSpans=[];
 const root=p.root;const acc=countObjs(root,{objs:0,comps:{}});
 const top=el('div','pfhead');
 const kinds=Object.entries(acc.comps).sort((a,b)=>b[1]-a[1]);
 top.append(el('div','','This prefab has '+acc.objs+' object'+(acc.objs>1?'s':'')+' and '+kinds.reduce((a,b)=>a+b[1],0)+' components.'));
 const pills=el('div','pfpills');for(const [k,n] of kinds){const s=el('span','pill',shortComp(k)+' × '+n);s.title=k;pills.append(s)}top.append(pills);
 const bar=el('div','mvbar');
 if(p.model){const b=el('button','btn','Open model');b.onclick=()=>follow(pkg,p.model);bar.append(b)}
 const ex=el('button','btn','Expand all'),co=el('button','btn','Collapse all');
 ex.onclick=()=>{let n=0;const go=()=>{const cl=[...body.querySelectorAll('details.obj:not([open]),details.rawn:not([open])')];cl.slice(0,400).forEach(d=>{d.open=true;n++});if(cl.length>400&&n<4000)setTimeout(go,60)};go()};
 co.onclick=()=>body.querySelectorAll('details').forEach(d=>{d.open=false});
 bar.append(ex,co);top.append(bar);body.append(top);reachStrip(body,pkg,path);
 // linked assets
 const links=el('details','pflinks');const ls=document.createElement('summary');ls.textContent='Linked files';links.append(ls);const lb=el('div');links.append(lb);body.append(links);
 const gs=new Map();collectGuids(root,gs);
 async function fillLinks(tries){let found={},fin=true;const ids=[...gs.keys()];
  for(let i=0;i<ids.length;i+=300){const r=await api('guids',{ids:ids.slice(i,i+300).join(',')});Object.assign(found,r.found);fin=fin&&r.finished}
  const byFile=new Map();let missing=0;for(const [g,n] of gs){const h=found[g];if(!h){missing+=n;continue}const k=h.pkg+'|'+h.path;const e=byFile.get(k)||{h,n:0};e.n+=n;byFile.set(k,e)}
  lb.textContent='';const rows=[...byFile.values()].sort((a,b)=>b.n-a.n);
  ls.textContent='Linked files ('+rows.length+(missing?', '+missing+' unresolved link'+(missing>1?'s':''):'')+(fin?'':', still indexing…')+')';
  const t=el('table','mt');for(const r of rows.slice(0,200)){const tr=el('tr');const a=el('span','link',r.h.path);a.onclick=()=>follow(r.h.pkg,r.h.path);const c1=el('td');c1.append(a);tr.append(c1,el('td','tg','× '+r.n));t.append(tr)}
  lb.append(t);if(rows.length>200)lb.append(el('div','tg','Showing the 200 most used.'));
  if(!fin&&tries<40)setTimeout(()=>fillLinks(tries+1),1500)}
 fillLinks(0).catch(()=>{});
 if(opts&&opts.raw){const t=await api('tree',{pkg,path});const w=el('div','rawtree');for(const k of (t.tree||t.c||[]))w.append(rawNodeEl(k,0));body.append(w);resolveChips(0)}else body.append(objEl(root,0));
}

/* ---- small still previews of models ---- */
let thumbGL=null,thumbQ=Promise.resolve();
function thumbSetup(){if(thumbGL)return thumbGL;const c=document.createElement('canvas');c.width=480;c.height=340;
 const gl=c.getContext('webgl2',{antialias:true,preserveDrawingBuffer:true});if(!gl)return null;
 const sh=(t,s)=>{const o=gl.createShader(t);gl.shaderSource(o,s);gl.compileShader(o);return o};
 const prog=gl.createProgram();gl.attachShader(prog,sh(gl.VERTEX_SHADER,VS));gl.attachShader(prog,sh(gl.FRAGMENT_SHADER,FS));gl.linkProgram(prog);
 const U=n=>gl.getUniformLocation(prog,n);
 return thumbGL={c,gl,prog,u:{mvp:U('mvp'),view:U('view'),model:U('model'),tex:U('tex'),col:U('col'),use:U('useTex'),flat:U('flatc'),lit:U('lit')}}}
function loadImg(url){return new Promise(res=>{const i=new Image();const t=setTimeout(()=>res(null),6000);i.onload=()=>{clearTimeout(t);res(i)};i.onerror=()=>{clearTimeout(t);res(null)};i.src=url})}
async function renderThumb(pkg,path,focus){
 const T=thumbSetup();if(!T)return null;const {gl,c,prog,u}=T;
 const m=await api('model',{pkg,path});if(!m.has_geometry||!m.meshes.length)return null;
 const lod=Math.min(...m.meshes.map(x=>x.lod));let ids=m.meshes.map((x,i)=>i).filter(i=>m.meshes[i].lod===lod&&!m.meshes[i].collider);
 if(focus&&m.nodes&&m.nodes[focus]){const k=new Set(m.nodes[focus]);const f=ids.filter(i=>k.has(i));if(f.length)ids=f}
 const hsl2=i=>hsl((i*67)%360,0.55,0.55);
 const slots=[...new Set(ids.map(i=>m.meshes[i].slot))];const imgs={};
 await Promise.all(slots.map(async sl=>{const mt=m.materials[sl];if(mt&&mt.texture)imgs[sl]=await loadImg(texUrl(mt.texture))}));
 const made=[],texs=[];const lo=[1e30,1e30,1e30],hi=[-1e30,-1e30,-1e30];const draws=[];
 for(const i of ids){const r=await fetch('/api/mesh?'+new URLSearchParams({pkg,path,i}));if(!r.ok)continue;const buf=await r.arrayBuffer();const dv=new DataView(buf);
  const nv=dv.getUint32(0,true),ni=dv.getUint32(4,true);const f=new Float32Array(buf,8,nv*15);const x=m.meshes[i],w=x.xf||[1,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1];
  const vao=gl.createVertexArray();gl.bindVertexArray(vao);const vb=gl.createBuffer();gl.bindBuffer(gl.ARRAY_BUFFER,vb);gl.bufferData(gl.ARRAY_BUFFER,new Uint8Array(buf,8,nv*60),gl.STATIC_DRAW);
  gl.enableVertexAttribArray(0);gl.vertexAttribPointer(0,3,gl.FLOAT,false,60,0);gl.enableVertexAttribArray(1);gl.vertexAttribPointer(1,3,gl.FLOAT,false,60,12);gl.enableVertexAttribArray(2);gl.vertexAttribPointer(2,2,gl.FLOAT,false,60,48);
  const ib=gl.createBuffer();gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER,ib);gl.bufferData(gl.ELEMENT_ARRAY_BUFFER,new Uint32Array(buf,8+nv*60,ni),gl.STATIC_DRAW);gl.bindVertexArray(null);
  made.push(vao,vb,ib);
  for(let k=0;k<nv;k++){const a=f[k*15],b=f[k*15+1],cc=f[k*15+2];for(let q=0;q<3;q++){const t=a*w[q]+b*w[4+q]+cc*w[8+q]+w[12+q];if(t<lo[q])lo[q]=t;if(t>hi[q])hi[q]=t}}
  draws.push({vao,ni,w,x})}
 if(!draws.length)return null;
 const cen=lo.map((v,a)=>(v+hi[a])/2),rad=Math.max(Math.hypot(hi[0]-lo[0],hi[1]-lo[1],hi[2]-lo[2])/2,1e-3),dist=rad*2.4,yaw=0.6,pitch=0.35,cp=Math.cos(pitch);
 const eye=[cen[0]+dist*cp*Math.sin(yaw),cen[1]+dist*Math.sin(pitch),cen[2]+dist*cp*Math.cos(yaw)];
 const view=M4.look(eye,cen,[0,1,0]),proj=M4.persp(0.8,c.width/c.height,dist*0.01+rad*0.002,dist+rad*40);
 gl.viewport(0,0,c.width,c.height);gl.clearColor(0.17,0.19,0.22,1);gl.clear(gl.COLOR_BUFFER_BIT|gl.DEPTH_BUFFER_BIT);gl.enable(gl.DEPTH_TEST);gl.useProgram(prog);
 gl.uniformMatrix4fv(u.mvp,false,M4.mul(proj,view));gl.uniformMatrix4fv(u.view,false,view);gl.uniform1i(u.tex,0);gl.uniform1f(u.lit,1);gl.uniform4f(u.flat,0,0,0,0);
 let ff=true;gl.frontFace(gl.CW);gl.enable(gl.POLYGON_OFFSET_FILL);gl.polygonOffset(1,1);
 for(const d of draws){gl.uniformMatrix4fv(u.model,false,new Float32Array(d.w));const cw=!d.x.flip;if(cw!==ff){ff=cw;gl.frontFace(cw?gl.CW:gl.CCW)}
  const im=imgs[d.x.slot];
  if(im){const t=gl.createTexture();texs.push(t);gl.activeTexture(gl.TEXTURE0);gl.bindTexture(gl.TEXTURE_2D,t);gl.texImage2D(gl.TEXTURE_2D,0,gl.RGBA,gl.RGBA,gl.UNSIGNED_BYTE,im);gl.generateMipmap(gl.TEXTURE_2D);
   gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MIN_FILTER,gl.LINEAR_MIPMAP_LINEAR);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_WRAP_S,gl.REPEAT);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_WRAP_T,gl.REPEAT);
   const tc=(m.materials[d.x.slot]||{}).color||[1,1,1,1];gl.uniform1f(u.use,1);gl.uniform4f(u.col,Math.min(1,tc[0]),Math.min(1,tc[1]),Math.min(1,tc[2]),1)}
  else{gl.uniform1f(u.use,0);gl.uniform4fv(u.col,hsl2(d.x.slot))}
  gl.bindVertexArray(d.vao);gl.drawElements(gl.TRIANGLES,d.ni,gl.UNSIGNED_INT,0)}
 gl.bindVertexArray(null);const url=c.toDataURL('image/png');
 for(let k=0;k<made.length;k+=3){gl.deleteVertexArray(made[k]);gl.deleteBuffer(made[k+1]);gl.deleteBuffer(made[k+2])}texs.forEach(t=>gl.deleteTexture(t));
 return {url,meshes:ids.length}}
const thumbCache=new Map();
function thumbEl(pkg,path,focus){const key=pkg+'|'+path+'|'+(focus||'');const box=el('div','thumb3d');box.textContent='…';
 if(!thumbCache.has(key))thumbCache.set(key,new Promise(res=>{thumbQ=thumbQ.then(()=>renderThumb(pkg,path,focus)).then(res,()=>res(null))}));
 thumbCache.get(key).then(r=>{box.textContent='';if(!r){box.textContent='no preview';box.classList.add('none');return}const i=new Image();i.src=r.url;i.alt=path;box.append(i)});return box}
async function reachStrip(body,pkg,path){
 let r;try{r=await api('reach',{pkg,path})}catch(e){return}
 if(!r.models.length)return;
 const sec=el('div','reach');sec.append(el('h4','','Models this links to ('+r.models.length+')'));
 const row=el('div','reachrow');sec.append(row);
 for(const mm of r.models.slice(0,12)){const card=el('div','rcard');card.append(thumbEl(mm.pkg,mm.path,mm.focus));
  const a=el('span','link',baseName(mm.path)+(mm.sub?' › '+mm.sub:''));a.onclick=()=>follow(mm.pkg,mm.path,mm.focus);card.append(a);
  card.append(el('div','tg',mm.chain.join(' → ')));row.append(card)}
 if(r.models.length>12)sec.append(el('div','tg','Showing 12 of '+r.models.length+'.'));
 body.append(sec)}
/* ---- links view: what this file uses / what uses it ---- */
function linkRow(r,ancestors,depth){
 const key=r.pkg+'|'+r.path;const d=document.createElement('details');d.className='lrow';const sm=document.createElement('summary');
 const a=el('span','link',baseName(r.path));a.title=r.pkg+' / '+r.path;a.onclick=e=>{e.preventDefault();e.stopPropagation();follow(r.pkg,r.path,r.focus)};sm.append(a);
 if(r.count)sm.append(el('span','tg','  × '+r.count));
 if(r.subs&&r.subs.length)sm.append(el('span','tg','  '+r.subs.join(', ')));
 const vv=(r.via||[]).filter(v=>v!=='file');if(vv.length)sm.append(el('span','tg','  (in '+vv.join(', ')+')'));
 sm.append(el('span','tg','   '+r.path.split('/').slice(0,-1).join('/')));
 d.append(sm);const b=el('div','lbody');d.append(b);let loaded=false;
 d.addEventListener('toggle',async()=>{if(!d.open||loaded)return;loaded=true;
  if(r.path.endsWith('.fbx'))b.append(thumbEl(r.pkg,r.path,r.focus));
  if(ancestors.has(key)){b.append(el('div','tg','(already shown above – circular link)'));return}
  if(depth>=8){b.append(el('div','tg','(stopping here, nesting is deep)'));return}
  try{const x=await api('links',{pkg:r.pkg,path:r.path,only:'uses'});const anc=new Set(ancestors);anc.add(key);
   if(!x.uses.length)b.append(el('div','tg','Does not point to any other file.'));
   x.uses.forEach(u=>b.append(linkRow(u,anc,depth+1)))}catch(e){b.append(el('div','tg',e.message))}});
 return d}
async function linksTab(body){
 const {pkg,path}=cur;const me=pkg+'|'+path;const r=await api('links',{pkg,path});
 const head=el('div','pfhead');body.append(head);reachStrip(head,pkg,path);
 const up=el('div');body.append(up);
 const h1=el('h4','','Uses ('+r.uses.length+' file'+(r.uses.length===1?'':'s')+')');body.append(h1);
 if(!r.links_ready)body.append(el('div','note','Still indexing links between files, so this list may be incomplete. Open the tab again in a moment.'));
 if(r.unresolved)body.append(el('div','note',r.unresolved+' link'+(r.unresolved>1?'s point':' points')+' to files that are not in the loaded packages.'));
 if(!r.uses.length)body.append(el('div','note','This file does not point to any other file.'));
 r.uses.forEach(u=>body.append(linkRow(u,new Set([me]),0)));
 const h2=el('h4','','Used by');body.insertBefore(h2,h1);const ub=el('div');body.insertBefore(ub,h1);
 function showUsedBy(x){ub.textContent='';
  if(!x.used_by_ready){ub.append(el('div','note','Scanning all files to find what uses this one… '+x.progress[0].toLocaleString()+' / '+x.progress[1].toLocaleString()+' (this takes a while on big packages; browsing still works).'));return false}
  h2.textContent='Used by ('+x.used_by.length+' file'+(x.used_by.length===1?'':'s')+')';
  if(!x.used_by.length)ub.append(el('div','note','No other file in the loaded packages points to this one.'));
  const t=el('div');x.used_by.slice(0,500).forEach(u=>{const row=el('div','mrow');const a=el('span','link',u.path);a.title=u.pkg;a.onclick=()=>follow(u.pkg,u.path);row.append(a);if(u.subs.length)row.append(el('span','tg','  → '+u.subs.join(', ')));t.append(row)});
  ub.append(t);if(x.used_by.length>500)ub.append(el('div','tg','Showing the first 500.'));return true}
 let x=r;const poll=async()=>{if(!body.isConnected)return;if(!showUsedBy(x)){await new Promise(z=>setTimeout(z,2500));if(!body.isConnected)return;x=await api('links',{pkg,path});poll()}};poll()}


/* ---- overview: values grouped by kind and drawn readably ---- */
const NUMT=['int','uint','float','double','int64','uint64'];
let rawNames=false;
function humanize(k){if(rawNames)return k;return k.replace(/_/g,' ').replace(/([a-z0-9])([A-Z])/g,'$1 $2').replace(/([A-Z]+)([A-Z][a-z])/g,'$1 $2').replace(/^\s*./,c=>c.toUpperCase())}
function fnum(v,t){if(typeof v!=='number')return String(v);if(t==='float'||t==='double')return String(+v.toPrecision(6));return Math.abs(v)>=100000?v.toLocaleString():String(v)}
function vmap(e){const m={};if(e.f&&e.f.length>1&&!(e.c&&e.c.length)){for(const f of e.f)m[f.tag]=f;return m}
 if(e.c&&e.c.length&&!(e.f&&e.f.length)&&e.c.every(k=>!(k.c&&k.c.length)&&k.f&&k.f.length===1&&NUMT.includes(k.f[0].type))){for(const k of e.c)m[k.n]=k.f[0];return m}
 return null}
function classify(e){const kids=e.c||[],own=e.f||[];
 if(!kids.length&&own.length===1){const t=own[0].type;
  if(t==='guid')return 'link';if(t==='string')return 'text';if(t==='bool')return 'flag';if(NUMT.includes(t))return 'num';if(t==='class')return 'class';return 'other'}
 const m=vmap(e);if(m){const ks=Object.keys(m);
  if(['r','g','b'].every(k=>k in m)&&ks.every(k=>'rgba'.includes(k)))return 'color';
  if(ks.every(k=>'xyzw'.includes(k))&&ks.length>=2)return 'vec';return 'struct-inline'}
 if(kids.length){const names=new Set(kids.map(k=>k.n));
  if(names.size===1&&(kids.length>1||/^Item$/i.test(kids[0].n)||/List|Array|s$/.test(e.n)))return 'list';return 'group'}

 if(!kids.length&&!own.length&&/List|Array|Items|Entries/.test(e.n))return 'list';
 return 'other'}
function colorBox(m,big){const c=k=>m[k]?+m[k].value:(k==='a'?1:0);const r=c('r'),g=c('g'),b=c('b'),a=c('a');
 const q=v=>Math.max(0,Math.min(255,Math.round(v*255)));const hex='#'+[r,g,b].map(v=>q(v).toString(16).padStart(2,'0')).join('').toUpperCase();
 const box=el('div','cbox'+(big?' big':''));const fill=el('div','cfill');fill.style.background='rgba('+q(r)+','+q(g)+','+q(b)+','+Math.max(0,Math.min(1,a))+')';box.append(fill);
 const w=el('div','cwrap');w.append(box);const t=el('div','ctext');t.append(el('b','',hex),document.createTextNode('  rgba('+[r,g,b].map(v=>+v.toPrecision(3)).join(', ')+', '+(+a.toPrecision(3))+')'));
 w.append(t);return w}
function vecText(m,name){const ks=['x','y','z','w'].filter(k=>k in m);const vs=ks.map(k=>fnum(m[k].value,m[k].type));
 if(ks.length===2&&/size|count|dimension|resolution/i.test(name))return vs.join(' × ');return '('+vs.join(', ')+')'}
function valueBits(e,kind){const n=valueBits0(e,kind);let t='';const own=(e.f||[])[0];
 if(kind==='vec'||kind==='struct-inline'){const m=vmap(e);t=[...new Set(Object.values(m).map(f=>f.type))].join('/')}else if(own)t=own.type;
 if(t&&n&&n.append)n.append(el('span','vtype',t));return n}
function valueBits0(e,kind){const own=(e.f||[])[0];
 if(kind==='text'){const sp=el('span','ovbox'+(/^[A-Z0-9_.\-]+$/.test(own.value)&&own.value.length>2?' ovkey':''),own.value);return sp}
 if(kind==='num')return el('span','ovnum',fnum(own.value,own.type));
 if(kind==='flag')return el('span','ovbox ovbool '+(own.value?'bt':'bf'),own.value?'true':'false');
 if(kind==='link'){if(own.value===ZERO_G)return el('span','tg','none');return guidChip(own.value)}
 if(kind==='class')return el('span','pill',own.value);
 if(kind==='vec'){return el('span','ovnum',vecText(vmap(e),e.n))}
 if(kind==='struct-inline'){const m=vmap(e);const sp=el('span','');sp.textContent=Object.entries(m).map(([k,f])=>k+' = '+(f.type==='guid'?f.value.slice(0,8)+'…':fnum(f.value,f.type))).join('   ');return sp}
 return el('span','tg',(e.f&&e.f.length)?e.f.map(f=>f.type+': '+f.value).join(', '):'empty')}
function ovTable(rows){const t=el('div','ovrows');for(const [label,node,raw] of rows){const r=el('div','ovrow');const l=el('span','ovlabel',label);if(raw&&raw!==label)l.title=raw;r.append(l,node);t.append(r)}return t}
const OVK={'Colors':'k-col','Strings':'k-str','Lists':'k-str','Values':'k-num','Other':'k-oth','Flags':'k-flag','GUID Links':'k-guid'};
function ovSection(title,count,body,collapsed){const d=el('details','ovsec ovfold '+(OVK[title]||'k-grp'));if(!collapsed)d.open=true;const sm=el('summary','ovsh');sm.append(el('span','ovst',title));if(count!==undefined)sm.append(el('span','tg',' '+count));d.append(sm,body);return d}
function ovListBlock(e){const kids=e.c||[];const b=el('div','ovlistblock');const h=el('div','ovlabel',humanize(e.n));if(kids.length)h.append(el('span','tg','  '+kids.length));b.append(h);
 const t=el('div','ovtable');if(!kids.length){const r=el('div','ovtr');r.append(el('span','ovbox ovmuted','empty'));t.append(r)}
 for(const k of kids){const r=el('div','ovtr');r.append(valueBits(k,classify(k)));t.append(r)}
 b.append(t);return b}
function ovList(e,depth){const kids=e.c||[];const wrap=el('div','ovlist');if(!kids.length){wrap.append(el('span','tg','empty'));return wrap}
 const allKind=kids.map(k=>classify(k));const same=allKind.every(k=>k===allKind[0])?allKind[0]:null;
 if(same==='link'){const g=el('div','ovgrid');for(const k of kids){if(k.f[0].value!==ZERO_G)g.append(guidChip(k.f[0].value))}wrap.append(g);return wrap}
 if(same==='color'){const g=el('div','ovgrid');for(const k of kids)g.append(colorBox(vmap(k),false));wrap.append(g);return wrap}
 if(['num','text','flag','class','vec'].includes(same)){const g=el('div','ovplainlist');for(const k of kids){const c=el('div','ovplain');c.append(valueBits(k,same));g.append(c)}wrap.append(g);return wrap}
 // key/value pairs
 if(kids.every(k=>k.c&&k.c.some(x=>x.n==='Key')&&k.c.some(x=>x.n==='Value'))){
  const rows=kids.map(k=>{const key=k.c.find(x=>x.n==='Key'),val=k.c.find(x=>x.n==='Value');const kd=el('span','ovkeycell');kd.append(valueBits(key,classify(key)));
   const body=el('div','ovkv');if(val.f&&val.f.length&&val.f[0].type==='class')body.append(el('div','tg',val.f[0].value));
   body.append(ovBody(val.c||[],depth+1,true));if(!(val.c&&val.c.length)&&classify(val)!=='class')body.append(valueBits(val,classify(val)));
   const r=el('div','ovkvrow');r.append(kd,body);return r});
  for(const r of rows)wrap.append(r);return wrap}
 kids.forEach((k,i)=>{const kk=classify(k);const cls=(k.f&&k.f.length)?k.f.map(f=>f.value).join(' '):'';
  const inner=(k.c&&k.c.length&&kk!=='color'&&kk!=='vec')?ovBody(k.c,depth+1,true):el('div','ovbody',null);
  if(!(k.c&&k.c.length&&kk!=='color'&&kk!=='vec'))inner.append(valueBits(k,kk));
  const sec=ovSection(k.n+(cls?' = '+cls:''),cls?'class':undefined,inner,true);sec.classList.add('ovitem');wrap.append(sec)});
 return wrap}
function ovBody(entries,depth,flat){const frag=el('div','ovbody');const closed=!(depth===0&&!flat&&entries.length===1);
 const simpleKinds=['num','text','flag','class','vec'];
 const isSimple=e=>{const k=e.c||[];if(!k.length)return true;const ks=k.map(classify);return ks.every(x=>x===ks[0])&&simpleKinds.includes(ks[0])};
 let run=null,runK=null;
 const flush=()=>{if(!run)return;if(runK==='scalar')frag.append(ovTable(run));else if(runK==='flag'){const t=el('div','ovtable ovflagtbl2');for(const r of run)t.append(r);frag.append(t)}else if(runK==='color'){const g=el('div','ovcolors');for(const r of run)g.append(r);frag.append(g)}run=null;runK=null};
 const push=(k,item)=>{if(runK!==k)flush();if(!run){run=[];runK=k}run.push(item)};
 for(const e of entries){const k=classify(e);
  if(k==='color'){const c=el('div','ovcolor');c.append(el('div','ovlabel',humanize(e.n)),colorBox(vmap(e),true));if(!rawNames)c.title=e.n;push('color',c)}
  else if(k==='list'&&isSimple(e)){flush();const h=el('div','ovtextbody');h.append(ovListBlock(e));frag.append(h)}
  else if(k==='list'){flush();frag.append(ovSection(humanize(e.n),(e.c||[]).length,ovList(e,depth),closed))}
  else if(k==='group'){flush();const inner=ovBody(e.c,depth+1,true);if(e.f&&e.f.length){const t=el('div','tg',e.f.map(f=>f.value).join(' '));inner.prepend(t)}frag.append(ovSection(humanize(e.n),undefined,inner,closed))}
  else{const vb=valueBits(e,k);vb.classList.add('v-'+k);push('scalar',[humanize(e.n),vb,e.n])}}
 flush();return frag}
const PF_SKIP=['name','id','assetId','transform','components','children'];
function pfPrune(a){const out=[];for(const e of a||[]){if(e.n==='id'&&e.f&&!(e.c&&e.c.length))continue;
 let c=e.c?pfPrune(e.c):e.c;
 if(c&&c.length&&c.every(k=>/^Item\d*$/.test(k.n))){c=c.map(k=>{const kk=(k.c||[]);return {n:'Item',f:(!kk.length&&k.f&&k.f.length)?k.f:(kk.length===1&&kk[0].f&&kk[0].f.length&&!(kk[0].c&&kk[0].c.length)?kk[0].f:undefined),c:(kk.length===1&&kk[0].f&&kk[0].f.length&&!(kk[0].c&&kk[0].c.length))?[]:kk}})}
 if((!e.f||!e.f.length)&&(!c||!c.length))continue;out.push(Object.assign({},e,{c:c}))}return out}
function pfObj(kids,lvl){lvl=lvl||0;const obj=kids.find(k=>k.n==='object'),chs=kids.find(k=>k.n==='children');if(!obj)return null;
 const parts={};for(const x of obj.c||[])parts[x.n]=x;
 const nm=parts.name&&parts.name.f?parts.name.f[0].value:'(unnamed)';
 const root=lvl<1;const card=el(root?'div':'details',root?'pfo pfroot':'pfo ovfold');const head=el(root?'div':'summary',root?'pfrooti':'pfoh');if(!root){head.append(el('b','',nm));}
 const act=(obj.c||[]).find(x=>x.n==='isActive');if(act&&act.f&&act.f[0].value===false)head.append(el('span','pill off','inactive'));
 if(parts.assetId&&parts.assetId.f&&parts.assetId.f[0].value!==ZERO_G){const w=el('span','tg','model part ');w.append(guidChip(parts.assetId.f[0].value));head.append(w)}
 if(!root||head.childNodes.length)card.append(head);const body=el('div','pfob');
 const tm=parts.transform?vmapKids(parts.transform):null;
 if(tm){const rows=[];const near1=(v,t)=>v.every(x=>Math.abs(x-t)<1e-4);
  if(tm.position&&!near1(Object.values(tm.position).map(f=>+f.value),0))rows.push(['Position',el('span','ovnum',vecText(tm.position,'position'))]);
  if(tm.rotation){const r=tm.rotation;const ident=['x','y','z'].every(k=>!r[k]||Math.abs(+r[k].value)<1e-4);if(!ident)rows.push(['Rotation',el('span','ovnum',vecText(r,'rotation'))])}
  if(tm.scale&&!['x','y','z'].every(k=>!tm.scale[k]||Math.abs(+tm.scale[k].value-1)<1e-4))rows.push(['Scale',el('span','ovnum',vecText(tm.scale,'scale'))]);
  if(rows.length)body.append(ovTable(rows))}
 const rest=pfPrune((obj.c||[]).filter(x=>!PF_SKIP.includes(x.n)&&x.n!=='isActive'));if(rest.length)body.append(ovBody(rest,1,true));
 const comps=parts.components?(parts.components.c||[]):[];const hasKids=!!(chs&&chs.c&&chs.c.length);
 if(comps.length&&hasKids)body.append(el('div','pfsub','Components'));
 for(const c of comps){const cb=el('details','pfc ovfold');const h=el('summary','pfch',shortComp(c.n));h.title=c.n;cb.append(h);
  const inner=pfPrune(c.c||[]);if(c.f&&c.f.length)inner.unshift(...c.f.map(f=>({n:f.tag||'value',f:[f]})));
  if(inner.length)cb.append(ovBody(inner,2,true));body.append(cb)}
 if(body.childNodes.length)card.append(body);
 if(chs&&chs.c&&chs.c.length){const kw=el('div','pfkids');kw.append(el('div','pfsub kids','Child objects · '+chs.c.length));for(const ch of chs.c){const o=pfObj(ch.c||[],lvl+1);if(o)kw.append(o)}if(kw.childNodes.length>1)(body.childNodes.length?body:card).append(kw)}
 return card}
function vmapKids(e){const out={};for(const k of e.c||[]){const m=vmap(k);if(m)out[k.n]=m}return out}
function pfCount(kids,acc){const obj=kids.find(k=>k.n==='object');if(!obj)return acc;acc.o++;const comps=((obj.c||[]).find(x=>x.n==='components')||{}).c||[];acc.c+=comps.length;
 const chs=kids.find(k=>k.n==='children');for(const ch of (chs&&chs.c)||[])pfCount(ch.c||[],acc);return acc}
async function overviewTab(body){
 const {pkg,path}=cur;const r=await api('tree',{pkg,path});chipSpans=[];
 const root=r.tree;const wrap=el('div','ov');
 const bar=el('div','ovbar');const l=el('label','');const cb=el('input');cb.type='checkbox';cb.checked=rawNames;l.append(cb,document.createTextNode(' Raw field names'));
 cb.onchange=()=>{rawNames=cb.checked;chipSpans=[];draw()};bar.append(l);wrap.append(bar);const host=el('div');wrap.append(host);body.append(wrap);
 function draw(){host.textContent='';chipSpans=[];
  if(root.length===1&&root[0].n==='root'&&(root[0].c||[]).some(k=>k.n==='object')){const acc=pfCount(root[0].c,{o:0,c:0});
   host.append(el('div','ovbar',acc.o+' object'+(acc.o===1?'':'s')+' · '+acc.c+' component'+(acc.c===1?'':'s')));
   const w=el('div','pf');w.append(pfObj(root[0].c));host.append(w);resolveChips(0);return}
  for(const top of root){
   const entries=top.c&&top.c.length?top.c:[];if(!entries.length){host.append(el('div','note','This file holds no further values.'))}else host.append(ovBody(entries,0));}
  resolveChips(0)}
 draw()}

/* ---- image preview: fits the panel, magnifier switches to true size ---- */
function imageView(b,cap,img){
 const wrap=el('div','imgv'),stage=el('div','imgstage'),btn=el('button','imgzoom','🔍');stage.append(img);wrap.append(stage,btn);b.append(cap,wrap);
 let full=false,base='';
 const upd=()=>{const nw=img.naturalWidth,nh=img.naturalHeight;if(!nw)return;
  const scaled=!full&&(img.clientWidth<nw-1||img.clientHeight<nh-1);
  wrap.classList.toggle('nofit',!full&&!scaled);
  cap.textContent=nw+' × '+nh+' px'+base+(scaled?' · fitted to '+Math.round(img.clientWidth/nw*100)+'%':full?' · true size':'');
  btn.textContent=full?'⤢ Fit':'🔍 True size';btn.title=full?'Scale the image to fit the panel':'Show the image at its true size'};
 const toggle=()=>{full=!full;wrap.classList.toggle('full',full);upd()};
 btn.onclick=toggle;img.onclick=()=>{if(!wrap.classList.contains('nofit')||full)toggle()};
 img.addEventListener('load',upd);window.addEventListener('resize',()=>{if(wrap.isConnected)upd()});
 return {setBase(t){base=t;upd()}}}
async function openFile(pkg,path,fromBack,focus){
 if(cur&&!fromBack&&!(cur.pkg===pkg&&cur.path===path)){hist.push(cur);}
 cur={pkg,path,base:'',focus:focus||null};$('#back').hidden=!hist.length;$('#title').textContent=pkg+' / '+path;$('#meta').textContent='';
 const info=await api('info',{pkg,path}).catch(e=>({error:e.message}));if(info.error){$('#body').textContent=info.error;return}
 cur.base=fmt(info.size)+' · '+info.kind;$('#meta').textContent=cur.base;
 const note=(m)=>b=>b.append(el('div','note',m));let tabs=[],links=[];
 if(info.kind==='container'){
  if(info.material)tabs.push(['Material',materialTab]);
  tabs.push(['Overview',overviewTab]);tabs.push(['Decoded',async b=>{if(info.prefab){await prefabTab(b,{raw:true})}else await loadNodes(b,pkg,path,4,0,0)}]);tabs.push(['Links',linksTab])}
 else if(info.kind==='text')tabs.push(['Text',async b=>{const r=await api('text',{pkg,path});const p=el('pre');p.textContent=r.text;b.append(p);if(r.truncated)b.append(el('div','note','Showing the first 1 MB only.'))}]);
 else if(info.kind==='image')tabs.push(['Image',async b=>{const i=el('img','pv');const c=el('div','note','');imageView(b,c,i);i.src=rawUrl(pkg,path)}]);
 else if(info.kind==='video')tabs.push(['Video',async b=>{const v=document.createElement('video');v.controls=true;v.style.maxWidth='100%';v.src=rawUrl(pkg,path);b.append(v)}]);
 else if(info.kind==='font')tabs.push(['Font',async b=>{const fam='f'+Date.now();const st=document.createElement('style');st.textContent='@font-face{font-family:'+fam+';src:url("'+rawUrl(pkg,path)+'")}';b.append(st);
   const s=el('div','','The quick brown fox jumps over the lazy dog 0123456789');s.style.cssText='font:32px '+fam+',serif;line-height:1.5';b.append(s)}]);
 else if(info.kind==='image-conv')tabs.push(['Image',async b=>{const i=el('img','pv');const c=el('div','note','Decoding… (large textures can take a few seconds)');const iv=imageView(b,c,i);
   const u='/api/png?'+new URLSearchParams({pkg,path});i.addEventListener('load',()=>iv.setBase(' (converted for display)'));
   i.onerror=async()=>{try{const r=await fetch(u);const j=await r.json();c.textContent=j.error||'Could not decode this image.'}catch(e){c.textContent='Could not decode this image.'}};i.src=u}]);
 else if(info.kind==='model'){tabs.push(['3D model',modelTab]);tabs.push(['Links',linksTab])}
 else tabs.push(['Preview',note('No preview for this kind of file yet. See the Hex tab for the raw bytes.')]);
 if(['image','image-conv','binary'].includes(info.kind))tabs.push(['Links',linksTab]);
 tabs.push(['Hex',hexTab]);setTabs(tabs,links)}
$('#back').onclick=()=>{const p=hist.pop();if(p){openFile(p.pkg,p.path,true,p.focus).then(()=>reveal(p.pkg,p.path))}};
let timer=null;$('#q').addEventListener('input',()=>{clearTimeout(timer);timer=setTimeout(runSearch,250)});
async function runSearch(){const q=$('#q').value.trim(),box=$('#results');
 if(!q){box.hidden=true;$('#tree').hidden=false;return}
 const r=await api('search',Object.assign({q},extP()));box.textContent='';const ul=el('ul');
 if(!r.results.length)box.append(el('div','note','No matches.'));
 for(const m of r.results){const li=el('li','res');const row=el('div','row',m.path.split('/').pop());row.title=m.pkg+' / '+m.path;const p=el('span','sz',m.pkg+' / '+m.path.split('/').slice(0,-1).join('/'));row.append(p);
  row.onclick=()=>{selectRow(row);openFile(m.pkg,m.path)};li.append(row);ul.append(li)}
 box.append(ul);if(r.truncated)box.append(el('div','note','Showing the first 300 matches. Narrow the search.'));box.hidden=false;$('#tree').hidden=true}
async function buildTree(){const roots=await api('roots',extP());const ul=el('ul');dirNodes={};selRow=null;
 for(const r of roots)ul.append(dirItem(r.pkg,'',r.pkg,r.files+' files'));const t=$('#tree');t.textContent='';
 if(!roots.length)t.append(el('div','note','No files of the selected type(s).'));t.append(ul);
 if(filt.size)for(const r of roots){const n=dirNodes[r.pkg+':'];if(n)await n.open()}
 await restoreOpen()}
async function applyFilter(){const b=$('#fbtn');b.textContent=filt.size?'Type: '+[...filt].map(e=>'.'+e).join(' ')+' ▾':'Filter by type ▾';b.classList.toggle('on',filt.size>0);
 for(const c of document.querySelectorAll('#fpanel input'))c.checked=filt.has(c.value);
 await buildTree();if(!$('#results').hidden||$('#q').value.trim())runSearch()}
(async()=>{const exts=await api('exts');const fp=$('#fpanel');
 const clr=el('button','btn','Clear filter');clr.onclick=()=>{filt=new Set();applyFilter()};fp.append(clr);
 const box=el('div','fl');fp.append(box);
 for(const x of exts){const l=el('label','fi');const c=el('input');c.type='checkbox';c.value=x.ext;
  c.onchange=()=>{c.checked?filt.add(x.ext):filt.delete(x.ext);applyFilter()};l.append(c,document.createTextNode(' '+(x.ext==='(none)'?'(no extension)':'.'+x.ext)+' '),el('span','sz',x.count.toLocaleString()));box.append(l)}
 $('#fbtn').onclick=()=>{fp.hidden=!fp.hidden};$('#expl').onclick=expandLevel;$('#coll').onclick=collapseLevel;
 $('#stcb').onchange=e=>document.body.classList.toggle('showtypes',e.target.checked);
 $('#sgcb').onchange=e=>{showGuids=e.target.checked;document.querySelectorAll('[data-guid]').forEach(applyGuidText)};
 const hm=$('#hmcb');hm.checked=hideMeta;hm.onchange=()=>{hideMeta=hm.checked;try{localStorage.setItem('hideMeta',hideMeta?'1':'0')}catch(e){}applyFilter()};
(async()=>{try{const rs=await api('roots',{});const nf=rs.reduce((a,r)=>a+r.files,0),sz=rs.reduce((a,r)=>a+(r.size||0),0);
  $('#appsub').textContent=rs.map(r=>r.pkg).join(' · ')+'  —  '+rs.length+' package'+(rs.length>1?'s':'')+', '+nf.toLocaleString()+' files'+(sz?', '+fmt(sz):'')}catch(e){}
 const idx=$('#idx');const poll=async()=>{let r;try{r=await api('guids',{ids:''})}catch(e){setTimeout(poll,3000);return}
  if(!r.finished){idx.className='busy';idx.textContent='Indexing links '+Math.round(100*r.done/Math.max(1,r.total))+'%'}
  else if(!r.refs_finished){idx.className='busy';idx.textContent='Finding what uses what '+Math.round(100*r.refs_done/Math.max(1,r.refs_total))+'%'}
  else{idx.className='ok';idx.textContent='Links ready';return}
  setTimeout(poll,1500)};poll()})();
 await buildTree()})().catch(e=>{$('#tree').textContent='Could not load: '+e.message});

</script></body></html>
'''


# ---------------------------------------------------------------- Entry point
def pause_if_needed(opened_by_double_click):
    """When started by double-click the console window would vanish before you could read a message."""
    if opened_by_double_click:
        try:
            input('\nPress Enter to close this window.')
        except (EOFError, KeyboardInterrupt):
            pass


def main():
    ap = argparse.ArgumentParser(description='Browse Foundation .package files in your web browser.')
    ap.add_argument('packages', nargs='*', help='.package files (default: every .package next to this script)')
    ap.add_argument('--port', type=int, default=8765)
    ap.add_argument('--no-browser', action='store_true', help="don't open the web page automatically")
    a = ap.parse_args()
    dbl = not a.packages
    paths = list(a.packages)
    if dbl:
        here = os.path.dirname(os.path.abspath(__file__))
        for folder in dict.fromkeys([here, os.getcwd()]):
            paths = sorted(os.path.join(folder, f) for f in os.listdir(folder) if f.lower().endswith('.package'))
            if paths:
                break
        if not paths:
            print('No .package files found next to browser.py (%s).' % here)
            print('Put browser.py in the same folder as game.package, or run:  python browser.py path/to/game.package')
            return pause_if_needed(True)
        print('Found: ' + ', '.join(os.path.basename(p) for p in paths))
    loaded = []
    for path in paths:
        try:
            print('Reading %s ...' % os.path.basename(path), flush=True)
            p = Package(path)
        except (OSError, FormatError, struct.error) as e:
            print('Skipping %s: %s' % (path, e))
            continue
        name, i = p.name, 2
        while name in PACKS:
            name = '%s-%d' % (p.name, i)
            i += 1
        p.name = name
        PACKS[name] = p
        loaded.append(p)
        print('Loaded %s: %d files' % (path, len(p.files)))
    if not PACKS:
        print('No usable packages. Nothing to browse.')
        return pause_if_needed(dbl)
    threading.Thread(target=GUIDS.build, args=(loaded,), daemon=True).start()
    srv = None
    for port in range(a.port, a.port + 11):
        try:
            srv = ThreadingHTTPServer(('127.0.0.1', port), Handler)
            break
        except OSError:
            continue
    if srv is None:
        print('Could not start a server on ports %d-%d. Is another copy already running?' % (a.port, a.port + 10))
        return pause_if_needed(dbl)
    url = 'http://localhost:%d' % srv.server_address[1]
    print('\nOpen %s in your web browser (it should open by itself). Close this window or press Ctrl+C to stop.' % url)
    print('(Building the link index from .meta files in the background; browsing works meanwhile.)')
    if not a.no_browser:
        threading.Timer(0.7, lambda: webbrowser.open(url)).start()
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print('\nStopped.')


if __name__ == '__main__':
    try:
        main()
    except Exception:  # keep the window open so the error can be read
        import traceback
        traceback.print_exc()
        if len(sys.argv) == 1:
            pause_if_needed(True)
