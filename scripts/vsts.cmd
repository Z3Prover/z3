md build
cd build
set
call "C:\Program Files (x86)\Microsoft Visual Studio\2017\Enterprise\VC\Auxiliary\Build\vcvars64.bat"
cmake -G "NMake Makefiles" ../
nmake
nmake test-z3
git pull https://github.com/z3prover/z3test z3test
cd z3test
