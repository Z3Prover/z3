sd edit dll\z3.def
sd edit dll\z3_dbg.def
cd dll
python mk_def.py
cd ..
sd edit Microsoft.Z3\native.cs
sd edit Microsoft.Z3\enumerations.cs
sd edit lib\api_log_macros.h
sd edit lib\api_log_macros.cpp
sd edit lib\api_commands.cpp
sd edit python\z3core.py
sd edit ml\z3.mli
sd edit ml\z3.ml
sd edit ml\z3_stubs.c
pushd lib
python api.py
popd
pushd Microsoft.Z3
python mk_z3consts.py
popd
pushd python
sd edit z3consts.py
python mk_z3consts.py
sd edit z3tactics.py
python mk_z3tactics.py
popd
pushd ml 
call build.cmd 32
popd
sd revert -a ...