@echo off
SETLOCAL

REM Script to compile the Z3 OCaml API
REM
REM Compiles byte and debug native code versions with debug info, optimized native code versions without
REM
REM Assumes that environment variables are set to provide access to the C and OCaml compilers

REM directory containing z3_api.h
set Z3SRC=%1

REM directory containing z3.dll
set Z3BIN=%2

REM directory containing debug z3.dll
set Z3BINDBG=%3

REM link Z3 statically or dynamically
set STATIC=false
REM set STATIC=true

if %STATIC% == true (
    set Z3LIB=z3lib.lib
    set Z3DBGLIB=z3lib.lib
) else (
    set Z3LIB=z3.lib
    set Z3DBGLIB=z3.lib
)

REM ocaml 3.11 and later calls the linker through flexlink
ocamlc -version >> ocaml_version
set /p OCAML_VERSION= <ocaml_version
del ocaml_version
if %OCAML_VERSION% GEQ 3.11 (
    set XCFLAGS=
) else (
    REM add /MT if building the multithreaded version
    set XCFLAGS=/nologo /DWIN32
)

set XINCLUDE=-ccopt -I%Z3SRC%
set XLIBPATH=/LIBPATH:%Z3BIN%
set XCDBG=-g %XCFLAGS% %XINCLUDE%
set XCOPT=-ccopt /Ox -ccopt /Oy- %XCFLAGS% %XINCLUDE%


REM z3_stubs.c z3_theory_stubs.c z3.mli z3.ml -> DBG z3_stubs.obj z3.{cmi,cmo,obj}
ocamlc -c %XCDBG% z3_stubs.c z3_theory_stubs.c z3.mli z3.ml
if errorlevel 1 goto :EOF

REM z3_stubs.c z3_theory_stubs.c z3.mli z3.ml -> DBG z3_stubs.obj z3.{cmi,cmx,obj}
ocamlopt -c %XCDBG% z3_stubs.c z3_theory_stubs.c z3.mli z3.ml
if errorlevel 1 goto :EOF

REM %Z3DBGLIB% z3.obj z3_stubs.obj z3_theory_stubs.obj -> libz3_dbg.lib:
lib /nologo %XLIBPATH% /out:libz3_dbg.lib %Z3BINDBG%\%Z3DBGLIB% z3.obj z3_stubs.obj z3_theory_stubs.obj
if errorlevel 1 goto :EOF

REM z3_stubs.c z3_theory_stubs.c z3.mli z3.ml -> OPT z3_stubs.obj z3.{cmi,cmx,obj}
ocamlopt -c %XCOPT% z3_stubs.c z3_theory_stubs.c z3.mli z3.ml
if errorlevel 1 goto :EOF

REM %Z3LIB% z3.obj z3_stubs.obj z3_theory_stubs.obj -> libz3.lib:
lib /nologo %XLIBPATH% /out:libz3.lib %Z3BIN%\%Z3LIB% z3.obj z3_stubs.obj z3_theory_stubs.obj
if errorlevel 1 goto :EOF


REM ole32.lib is needed by camlidl
REM camlidl.lib is the runtime library for camlidl
REM psapi.lib is needed when statically linking Z3 for process statistics functions

REM libz3_dbg.lib ole32.lib camlidl.lib z3.cmo -> z3_dbg.cma
ocamlc -custom -a %XCDBG% -cclib -L"%CD%\..\bin" -cclib -lz3_dbg -cclib ole32.lib -cclib -lcamlidl -cclib psapi.lib z3.cmo -o z3_dbg.cma
if errorlevel 1 goto :EOF

REM libz3.lib ole32.lib camlidl.lib z3.cmo -> z3.cma
ocamlc -custom -a -cclib -L"%CD%\..\bin" -cclib -lz3 -cclib ole32.lib -cclib -lcamlidl -cclib psapi.lib z3.cmo -o z3.cma
if errorlevel 1 goto :EOF


REM libz3_dbg.lib ole32.lib camlidl.lib z3.cmx -> z3_dbg.cmxa
ocamlopt -a -cclib -L"%CD%\..\bin" -cclib -lz3_dbg -cclib ole32.lib -cclib -lcamlidl -cclib psapi.lib z3.cmx -o z3_dbg.cmxa
if errorlevel 1 goto :EOF

REM libz3.lib ole32.lib camlidl.lib z3.cmx -> z3.cmxa
ocamlopt -a -cclib -L"%CD%\..\bin" -cclib -lz3 -cclib ole32.lib -cclib -lcamlidl -cclib psapi.lib z3.cmx -o z3.cmxa
if errorlevel 1 goto :EOF


REM build OCaml toplevel 'ocamlz3' pre-linked with Z3
ocamlmktop -o ocamlz3 z3.cma
if errorlevel 1 goto :EOF


del /q 2>NUL z3.cmo z3.cmx *.obj

ENDLOCAL
