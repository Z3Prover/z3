WARNING: this example still uses the old Z3 (version 3.x) C API. 
The current version is backward compatible. 

This directory contains scripts to build the MaxSAT application using
Microsoft C compiler, or gcc.

1) Using Microsoft C compiler (with binary release)

Use 'build.cmd' to build the MaxSAT application using Microsoft C compiler.

Remark: The Microsoft C compiler (cl) must be in your path,
or you can use the Visual Studio Command Prompt.

The script 'exec.cmd' adds the bin directory to the path. So, 
maxsat.exe can find z3.dll.

