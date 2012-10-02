WARNING: this example still uses the old Z3 (version 3.x) C API. The current version is backward compatible. Please go to the examples/c++ for examples using the new API.  

This directory contains scripts to build the test application using
Microsoft C compiler, or gcc.

1) Using Microsoft C compiler

Use 'build.cmd' to build the test application using Microsoft C
compiler.

Remark: The Microsoft C compiler (cl) must be in your path,
or you can use the Visual Studio Command Prompt.

The script 'exec.cmd' adds the bin directory to the path. So, 
test_capi.exe can find z3.dll.


2) Using gcc

Use 'build.sh' to build the test application using gcc. 
The script 'exec.sh' adds the bin directory to the path. So, 
test_capi.exe can find z3.dll.

Remark: the scripts 'build.sh' and 'exec.sh' assumes you are in a
Cygwin or Mingw shell.

