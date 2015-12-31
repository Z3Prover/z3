To use CLion as an IDE, you need to build Z3 with CMake.

* First build Z3 using the normal method.  We need the python build
  system to generate files in src/

  $ ./configure [--java]
  $ cd build; make

* Then run mk-cmake.sh.  This will generate the file lists that will
  be consumed by CMake.

* Build, run, debug the code from CLion.
