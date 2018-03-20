echo "Build"
md build
cd build
call "C:\Program Files (x86)\Microsoft Visual Studio\2017\Enterprise\VC\Auxiliary\Build\vcvars64.bat"
cmake -DBUILD_DOTNET_BINDINGS=True -DBUILD_JAVA_BINDINGS=True -DBUILD_PYTHON_BINDINGS=True -G "NMake Makefiles" ../
nmake
rem TBD: test error level

echo "Test python bindings"
pushd python
python z3test.py z3
python z3test.py z3num
popd

echo "Build and run examples"
nmake cpp_example
cpp_example.exe

nmake c_example
c_example.exe

nmake java_example
java_example.exe

nmake dotnet_example
dotnet_example.exe


echo "Build and run unit tests"
nmake test-z3
rem TBD: test error level
rem test-z3.exe -a


cd ..
echo "Run regression tests"
git clone https://github.com/z3prover/z3test z3test
z3test\scripts\test_benchmarks.py build\z3.exe z3test\regressions\smt2


