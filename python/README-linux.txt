In your Python application you should include:

   from z3 import *

Installing the Z3 Python bindings

Option 1: Install Z3 Python bindings in your python distribution
----------------------------------------------------------------

To install the Z3 python bindings in your system, use
   sudo make install-python 
in the Z3 root directory.
After installing the Z3 python bindings, you can try the example application
   python example.py

Option 2: Set PYTHONPATH
------------------------

You may also use Z3Py by including this directory in your PYTHONPATH.
Z3Py searches for libz3.so in set of predefined places that includes the directory where Z3Py is stored.
You may also manually initialize Z3Py using the command z3.init(path-to-libz3.so)

Learn more about Z3Py at:
http://rise4fun.com/Z3Py/tutorial/guide


