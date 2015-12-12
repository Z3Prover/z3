# Z3

Z3 is a theorem prover from Microsoft Research.
Z3 is licensed under the MIT license.
Z3 can be built using Visual Studio Command Prompt and make/g++.

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

## Building Z3 using make/g++ and Python

Execute:

```bash
   python scripts/mk_make.py
   cd build
   make
   sudo make install
```

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

## Building Z3 using clang and clang++ on Linux/OSX
Remark: clang does not support OpenMP yet.

```bash
   CXX=clang++ CC=clang python scripts/mk_make.py
   cd build
   make
```

To clean Z3 you can delete the build directory and run the ``mk_make.py`` script again.
