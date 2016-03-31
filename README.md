# Z3

Z3 is a theorem prover from Microsoft Research. It is licensed
under the [MIT license](LICENSE.txt).

If you are not familiar with Z3, you can start [here](https://github.com/Z3Prover/z3/wiki#background).

Z3 can be built using [Visual Studio][1], a [Makefile][2] or using [CMake][3]. It provides
[bindings for several programming languages][4].

See the [release notes](RELEASE_NOTES) for notes on various stable releases of Z3.

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

Note by default ``gcc`` is used as the C++ compiler if it is available. If you
would prefer to use Clang change the ``mk_make.py`` line to

```bash
CXX=clang++ CC=clang python scripts/mk_make.py
```

Note that Clang < 3.7 does not support OpenMP.

By default, it will install z3 executable at ``PREFIX/bin``, libraries at
``PREFIX/lib``, and include files at ``PREFIX/include``, where ``PREFIX``
installation prefix if inferred by the ``mk_make.py`` script. It is usually
``/usr`` for most Linux distros, and ``/usr/local`` for FreeBSD and OSX. Use
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
``make uninstall`` will remove the dll from the GAC and the pkg-config file.

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
and install Z3 there.

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
