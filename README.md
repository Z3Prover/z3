# Z3

Z3 is a theorem prover from Microsoft Research. It is licensed
under the [MIT license](LICENSE.txt).

If you are not familiar with Z3, you can start [here](https://github.com/Z3Prover/z3/wiki#background).

Pre-built binaries for releases are available from [here](https://github.com/Z3Prover/z3/releases), 
and nightly builds from [here](https://github.com/Z3Prover/bin/tree/master/nightly).

Z3 can be built using [Visual Studio][1], a [Makefile][2] or using [CMake][3]. It provides
[bindings for several programming languages][4]. 

See the [release notes](RELEASE_NOTES) for notes on various stable releases of Z3.

## Build status

| Windows x64 | Windows x86 | Windows x64 | Ubuntu x64 | Debian x64 | macOS | TravisCI |
| ----------- | ----------- | ----------- | ---------- | ---------- | ----- | -------- |
[![win64-badge](https://z3build.visualstudio.com/_apis/public/build/definitions/2e0aa542-a22c-4b1a-8dcd-3ebae8e12db4/4/badge)](https://z3build.visualstudio.com/Z3Build/_build/index?definitionId=4) | [![win32-badge](https://cz3.visualstudio.com/_apis/public/build/definitions/bf14bcc7-ebd4-4240-812c-5972fa59e0ad/4/badge)](https://cz3.visualstudio.com/Z3/_build/index?definitionId=4) | [![win64-badge](https://cz3.visualstudio.com/_apis/public/build/definitions/bf14bcc7-ebd4-4240-812c-5972fa59e0ad/7/badge)](https://cz3.visualstudio.com/Z3/_build/index?definitionId=7) | [![ubuntu-x64-badge](https://cz3.visualstudio.com/_apis/public/build/definitions/bf14bcc7-ebd4-4240-812c-5972fa59e0ad/3/badge)](https://cz3.visualstudio.com/Z3/_build/index?definitionId=3) | [![debian-badge](https://cz3.visualstudio.com/_apis/public/build/definitions/bf14bcc7-ebd4-4240-812c-5972fa59e0ad/5/badge)](https://cz3.visualstudio.com/Z3/_build/index?definitionId=5) | [![Build status](https://cz3.visualstudio.com/Z3/_apis/build/status/OSX)](https://cz3.visualstudio.com/Z3/_build/latest?definitionId=2) | [![Build Status](https://travis-ci.org/Z3Prover/z3.svg?branch=master)](https://travis-ci.org/Z3Prover/z3)

[1]: #building-z3-on-windows-using-visual-studio-command-prompt
[2]: #building-z3-using-make-and-gccclang
[3]: #building-z3-using-cmake
[4]: #z3-bindings

## Building Z3 on Windows using Visual Studio Command Prompt

32-bit builds, start with:

```bash
python scripts/mk_make.py
```

or instead, for a 64-bit build:

```bash
python scripts/mk_make.py -x
```

then:

```bash
cd build
nmake
```

## Building Z3 using make and GCC/Clang

Execute:

```bash
python scripts/mk_make.py
cd build
make
sudo make install
```

Note by default ``g++`` is used as the C++ compiler if it is available. If you
would prefer to use Clang change the ``mk_make.py`` invocation to:

```bash
CXX=clang++ CC=clang python scripts/mk_make.py
```

Note that Clang < 3.7 does not support OpenMP.

You can also build Z3 for Windows using Cygwin and the Mingw-w64 cross-compiler.
To configure that case correctly, make sure to use Cygwin's own python and not
some Windows installation of Python.

For a 64 bit build (from Cygwin64), configure Z3's sources with
```bash
CXX=x86_64-w64-mingw32-g++ CC=x86_64-w64-mingw32-gcc AR=x86_64-w64-mingw32-ar python scripts/mk_make.py
```
A 32 bit build should work similarly (but is untested); the same is true for 32/64 bit builds from within Cygwin32.

By default, it will install z3 executable at ``PREFIX/bin``, libraries at
``PREFIX/lib``, and include files at ``PREFIX/include``, where ``PREFIX``
installation prefix if inferred by the ``mk_make.py`` script. It is usually
``/usr`` for most Linux distros, and ``/usr/local`` for FreeBSD and macOS. Use
the ``--prefix=`` command line option to change the install prefix. For example:

```bash
python scripts/mk_make.py --prefix=/home/leo
cd build
make
make install
```

To uninstall Z3, use

```bash
sudo make uninstall
```

To clean Z3 you can delete the build directory and run the ``mk_make.py`` script again.

## Building Z3 using CMake

Z3 has an unofficial build system using CMake. Read the [README-CMake.md](README-CMake.md)
file for details.

## Z3 bindings

Z3 has bindings for various programming languages.

### ``.NET``

Use the ``--dotnet`` command line flag with ``mk_make.py`` to enable building these.

On non-windows platforms [mono](http://www.mono-project.com/) is required. On these
platforms the location of the C# compiler and gac utility need to be known. You
can set these as follows if they aren't detected automatically. For example:

```bash
CSC=/usr/bin/csc GACUTIL=/usr/bin/gacutil python scripts/mk_make.py --dotnet
```

Note for very old versions of Mono (e.g. ``2.10``) you may need to set ``CSC``
to ``/usr/bin/dmcs``.

Note that when ``make install`` is executed on non-windows platforms the GAC
utility is used to install ``Microsoft.Z3.dll`` into the
[GAC](http://www.mono-project.com/docs/advanced/assemblies-and-the-gac/) as the
``Microsoft.Z3.Sharp`` package. During install a
[pkg-config](http://www.freedesktop.org/wiki/Software/pkg-config/) file
(``Microsoft.Z3.Sharp.pc``) is also installed which allows the
[MonoDevelop](http://www.monodevelop.com/) IDE to find the bindings. Running
``make uninstall`` will remove the dll from the GAC and the ``pkg-config`` file.

See [``examples/dotnet``](examples/dotnet) for examples.

### ``C``

These are always enabled.

See [``examples/c``](examples/c) for examples.

### ``C++``

These are always enabled.

See [``examples/c++``](examples/c++) for examples.

### ``Java``

Use the ``--java`` command line flag with ``mk_make.py`` to enable building these.

See [``examples/java``](examples/java) for examples.

### ``OCaml``

Use the ``--ml`` command line flag with ``mk_make.py`` to enable building these.

See [``examples/ml``](examples/ml) for examples.

### ``Python``

Use the ``--python`` command line flag with ``mk_make.py`` to enable building these.

Note that is required on certain platforms that the Python package directory
(``site-packages`` on most distributions and ``dist-packages`` on Debian based
distributions) live under the install prefix. If you use a non standard prefix
you can use the ``--pypkgdir`` option to change the Python package directory
used for installation. For example:

```bash
python scripts/mk_make.py --prefix=/home/leo --python --pypkgdir=/home/leo/lib/python-2.7/site-packages
```

If you do need to install to a non standard prefix a better approach is to use
a [Python virtual environment](https://virtualenv.readthedocs.org/en/latest/)
and install Z3 there. Python packages also work for Python3.
Under Windows, recall to build inside the Visual C++ native command build environment.
Note that the ``build/python/z3`` directory should be accessible from where python is used with Z3 
and it depends on ``libz3.dll`` to be in the path.

```bash
virtualenv venv
source venv/bin/activate
python scripts/mk_make.py --python
cd build
make
make install
# You will find Z3 and the Python bindings installed in the virtual environment
venv/bin/z3 -h
...
python -c 'import z3; print(z3.get_version_string())'
...
```

See [``examples/python``](examples/python) for examples.

### ``Web Assembly``

[WebAssembly](https://github.com/cpitclaudel/z3.wasm) bindings are provided by Cl�ment Pit-Claudel.
