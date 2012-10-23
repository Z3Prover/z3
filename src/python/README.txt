You can learn more about Z3Py at:
http://rise4fun.com/Z3Py/tutorial/guide

On Windows, you must build Z3 before using Z3Py.
To build Z3, you should executed the following command
in the Z3 root directory at the Visual Studio Command Prompt

       msbuild /p:configuration=external

If you are using a 64-bit Python interpreter, you should use

       msbuild /p:configuration=external /p:platform=x64


On Linux and OSX, you must install Z3Py, before trying example.py.
To install Z3Py on Linux and OSX, you should execute the following 
command in the Z3 root directory

        sudo make install-z3py

