rem Build
md build
cd build
call "C:\Program Files (x86)\Microsoft Visual Studio\2017\Enterprise\VC\Auxiliary\Build\vcvars64.bat"
cmake -DBUILD_DOTNET_BINDINGS=True -DBUILD_JAVA_BINDINGS=True -DBUILD_PYTHON_BINDINGS=True -G "NMake Makefiles" ../
nmake

rem test python bindings
pushd python
python z3test.py z3
python z3test.py z3num
popd

rem Build and run examples



rem Build and run unit tests
nmake test-z3
test-z3.exe -a


cd ..
rem Run regression tests
rem git pull https://github.com/z3prover/z3test z3test
rem cd z3test
