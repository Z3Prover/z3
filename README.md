# Z3

Z3 is a theorem prover from Microsoft Research. It is licensed
under the [MIT license](LICENSE.txt).

Z3 can be built using [Visual Studio][1] or a [Makefile][2]. It provides
[bindings for several programming languages][3].

[1]: #building-z3-on-windows-using-visual-studio-command-prompt
[2]: #building-z3-using-make-and-gccclang
[3]: #z3-bindings

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

Note the above will typically disable the installation of the Python bindings
because the Python ``site-packages``  directory (e.g.
``/usr/lib/python3.5/site-packages/``) is not rooted in the install prefix and
installing outside of the install prefix is dangerous and misleading.

To avoid this issue you can use the ``DESTDIR`` makefile variable and leave the
install prefix as the default. The ``DESTDIR`` variable is prepended to the
install locations during ``make install`` and ``make uninstall`` and is intended
to allow ["staged installs"](https://www.gnu.org/prep/standards/html_node/DESTDIR.html).
Therefore it must always contain a trailing slash.

For example:

```bash
python scripts/mk_make.py
cd build
make
make install DESTDIR=/home/leo/
```

In this example, the Z3 Python bindings will be stored at
``/home/leo/lib/pythonX.Y/site-packages``
(``/home/leo/lib/pythonX.Y/dist-packages`` on Debian based Linux
distributions) where X.Y corresponds to the python version in your system.

To uninstall Z3, use

```bash
sudo make uninstall
```

To clean Z3 you can delete the build directory and run the ``mk_make.py`` script again.

## Z3 bindings

Z3 has bindings for various programming languages.

### ``.NET``

These bindings are enabled by default on Windows and are enabled on other
platforms if [mono](http://www.mono-project.com/) is detected. On these
platforms the location of the C# compiler and gac utility need to be known. You
can set these as follows if they aren't detected automatically. For example:

```bash
CSC=/usr/bin/csc GACUTIL=/usr/bin/gacutil python scripts/mk_make.py
```

To disable building these bindings pass ``--nodotnet`` to ``mk_make.py``.

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

These bindings are always enabled.

See [``examples/python``](examples/python) for examples.
