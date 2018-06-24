rem Supply argument x64 or x86

echo "Build"
md build
cd build
call "C:\Program Files (x86)\Microsoft Visual Studio\2017\Enterprise\VC\Auxiliary\Build\vcvarsall.bat" %1
cmake -DBUILD_DOTNET_BINDINGS=True -DBUILD_JAVA_BINDINGS=True -DBUILD_PYTHON_BINDINGS=True -G "NMake Makefiles" ../
nmake
if ERRORLEVEL 1 exit 1

if %1 == "x86" goto :BUILD_EXAMPLES
echo "Test python bindings"
pushd python
python z3test.py z3
if ERRORLEVEL 1 exit 1
python z3test.py z3num
if ERRORLEVEL 1 exit 1
popd

:BUILD_EXAMPLES
echo "Build and run examples"
nmake cpp_example
examples\cpp_example_build_dir\cpp_example.exe
if ERRORLEVEL 1 exit 1

nmake c_example
examples\c_example_build_dir\c_example.exe
if ERRORLEVEL 1 exit 1

rem nmake java_example
rem java_example.exe
if ERRORLEVEL 1 exit 1

rem nmake dotnet_example
rem dotnet_example.exe
if ERRORLEVEL 1 exit 1

echo "Build and run unit tests"
nmake test-z3
rem TBD: test error level
rem test-z3.exe -a


cd ..
echo "Run regression tests"
git clone https://github.com/z3prover/z3test z3test
echo "test-benchmarks"
python z3test\scripts\test_benchmarks.py build\z3.exe z3test\regressions\smt2
if ERRORLEVEL 1 exit 1
echo "benchmarks tested"

