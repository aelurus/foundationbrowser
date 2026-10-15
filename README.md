# foundationbrowser
Allows users to view and export .package files from the game Foundation.

Based on the code from https://gitlab.com/pegasusepsilon/foundation-package-tools

Updated for Foundation 1.12.0.14 

-----

To use -

Place browser.py in the root game folder (same folder as game.package, loading.package etc). Running browser.py with Python will open a Python terminal window, and a browser window.
The file browser will only work while the Python file is running.

The package browser tab lets you look at the files, preview models and textures, see what is linked to what file.

The file tree panel can filter files by name and type.

The inspector panel shows an overview of the selected file, the decoded original file, what other files it is used by/uses, and the raw hex code.


-----

I am planning on extending the functionality to repackage .package files.
