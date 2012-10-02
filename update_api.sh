#!/bin/sh
cd dll
python mk_def.py
cd ..
cd lib
python api.py
cd ..
cd Microsoft.Z3
python mk_z3consts.py
cd ..
cd python
python mk_z3consts.py
python mk_z3tactics.py
cd ..
