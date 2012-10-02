To run the test script execute:
python example.py

To create scripts using Z3Py, the Z3 python directory must be in your PYTHONPATH.
If you copy the z3*.py files to a different directory, you must also copy the z3.dll.
Remark: if you are using python 32-bit, you must copy the z3.dll in the bin directory. 
If you are using python 64-bit, you must copy the z3.dll in the x64 directory.

You may also manually initialize Z3Py using the command z3.init(path-to-z3.dll)

In your Python application you should include:

   from z3 import *

Learn more about Z3Py at:
http://rise4fun.com/Z3Py/tutorial/guide
