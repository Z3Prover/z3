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
installation prefix used for installing Python in your system.

It is usually ``/usr`` for most Linux distros, and ``/usr/local`` for FreeBSD.
Use the following commands to install in a different prefix (e.g., /home/leo)

```bash
  python scripts/mk_make.py --prefix=/home/leo
  cd build
  make
  make install
```

In this example, the Z3 Python bindings will be stored at ``/home/leo/lib/pythonX.Y/dist-packages``,
where X.Y corresponds to the python version in your system.

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
