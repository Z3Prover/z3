This directory contains scripts to build the test application using
Microsoft C compiler, or g++.

1) Using Microsoft C compiler

Use 'build.cmd' to build the test application using Microsoft C
compiler.

Remark: The Microsoft C compiler (cl) must be in your path,
or you can use the Visual Studio Command Prompt.

The script 'exec.cmd' adds the bin directory to the path. So, 
example.exe can find z3.dll.

2) Using gcc

You must install Z3 before running this example.
To install Z3, execute the following command in the Z3 root directory.

  sudo make install

Use 'build.sh' to build the test application using g++. 
It generates the executable 'example'.

