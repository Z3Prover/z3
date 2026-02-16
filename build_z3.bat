@echo off
REM Z3 Build Script

echo Checking for build directory...
if not exist C:\z3\build (
    echo Creating build directory...
    mkdir C:\z3\build
) else (
    echo Build directory already exists
)

echo Changing to build directory...
cd /d C:\z3\build

echo Running CMake configuration...
cmake ..
if errorlevel 1 (
    echo CMake configuration failed!
    exit /b 1
)

echo Building Z3 with parallel 8...
cmake --build . --parallel 8
if errorlevel 1 (
    echo Build failed!
    exit /b 1
)

echo Build completed successfully!
exit /b 0
