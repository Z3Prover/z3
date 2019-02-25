On Windows, to build Z3, you should executed the following command
in the Z3 root directory at the Visual Studio Command Prompt

       msbuild /p:configuration=external

If you are using a 64-bit Python interpreter, you should use

       msbuild /p:configuration=external /p:platform=x64


On Linux and macOS, you must install python bindings, before trying example.py.
To install python on Linux and macOS, you should execute the following
command in the Z3 root directory

        sudo make install-z3py

