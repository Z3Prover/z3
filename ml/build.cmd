@echo off
SETLOCAL

REM Script to generate, compile, test, and document the Z3 OCaml API
REM
REM Assumes that environment variables are set to provide access to the C and OCaml compilers, including flexdll and camlidl, as well as the following commands: diff, dos2unix, grep, sed, unix2dos
REM
REM usage: build.cmd [32|64] [-D UNSAFE_ERRORS] [-D LEAK_CONTEXTS]
REM
REM Invoke with "-D UNSAFE_ERRORS" to build version that does not support recoverable errors, but avoids some error-checking overhead.
REM Invoke with "-D LEAK_CONTEXTS" to build version that leaks Z3_context objects, but avoids some garbage-collection overhead.

if ""%1 == "" (
  set BITS=32
) else (
  set BITS=%1
)

if %BITS% == 32 (
  set ARCH=x86
  set Z3BIN= ..\external
  set Z3DBG= ..\Debug
) else (
  set ARCH=x64
  set Z3BIN= ..\x64\external_64
  set Z3DBG= ..\x64\Debug
)

echo { Cleaning
call .\clean.cmd
echo }

echo { Generating OCaml API %3 %5
call .\generate_mlapi.cmd %2 %3 %4 %5
if errorlevel 1 goto :EOF
echo }

echo { Compiling OCaml API
call .\compile_mlapi.cmd ..\lib %Z3BIN% %Z3DBG%
if errorlevel 1 goto :EOF
echo }

echo { Testing OCaml API
call .\test_mlapi.cmd ..\lib %Z3BIN% %Z3DBG%
if errorlevel 1 goto :EOF
echo }

echo { Generating OCaml API documentation
call .\update-ml-doc.cmd ..\doc
if errorlevel 1 goto :EOF
echo }

ENDLOCAL
