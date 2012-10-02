The script exec.sh sets PYTHONPATH, and executes 'python example.py'.

To create scripts using Z3Py, the Z3 python directory must be in your PYTHONPATH.
Z3Py searches for libz3.dylib in set of predefined places that includes the directory where Z3Py is stored.
You may also manually initialize Z3Py using the command z3.init(path-to-libz3.dylib)

In your Python application you should include:

   from z3 import *

Learn more about Z3Py at:
http://rise4fun.com/Z3Py/tutorial/guide
