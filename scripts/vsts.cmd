rem Build
md build
cd build
call "C:\Program Files (x86)\Microsoft Visual Studio\2017\Enterprise\VC\Auxiliary\Build\vcvars64.bat"
cmake -G "NMake Makefiles" ../
nmake

rem Run unit tests
nmake test-z3
test-z3.exe -a

cd ..
rem Run regression tests
git pull https://github.com/z3prover/z3test z3test
cd z3test
