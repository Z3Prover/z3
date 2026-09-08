@echo off
REM Z3 Build Script

echo Running CMake configuration...
cmake -S C:\z3 -B C:\z3\build
if errorlevel 1 (
    echo CMake configuration failed!
    exit /b 1
)

echo Building Z3 with parallel 8...
cmake --build C:\z3\build --parallel 8
if errorlevel 1 (
    echo Build failed!
    exit /b 1
)

echo Build completed successfully!
exit /b 0
