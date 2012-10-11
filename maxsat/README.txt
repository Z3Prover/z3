WARNING: this example still uses the old Z3 (version 3.x) C API. 
The current version is backward compatible. 

This directory contains scripts to build the MaxSAT application using
Microsoft C compiler, or gcc.

1) Using Visual Studio (with Z3 source code release)

The maxsat example application is automatically built when the z3-prover.sln is processed. The following command should be used to compile z3-prover.sln in the Z3 root directory

        msbuild /p:configuration=external

The maxsat executable is located at
    
        ..\external\maxsat

To process ex.smt, use

        ..\external\maxsat ex.smt

2) Using gcc (on Linux or OSX)

Use 'build.sh' to build the MaxSAT application using gcc. 

You must install Z3 before running this example.
To install Z3, execute the following command in the Z3 root directory.

  sudo make install

Use 'build.sh' to build the test application using gcc. 
It generates the executable 'maxsat'.
