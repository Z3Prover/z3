pushd dll
python mk_def.py
popd
pushd lib
python api.py
popd
pushd Microsoft.Z3
python mk_z3consts.py
popd
pushd python
python mk_z3consts.py
python mk_z3tactics.py
popd
