md build
cd build
set
"C:\Program Files (x86)\Microsoft Visual Studio\2017\Enterprise\VC\Auxiliary\Build\vcvars64.bat"
%VS140COMNTOOLS%\vcvars64.bat
cmake -G "NMake Makefiles" ../
nmake
