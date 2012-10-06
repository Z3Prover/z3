@echo off
SETLOCAL

REM Script to test the Z3 OCaml API
REM
REM Assumes that environment variables are set to provide access to the C and OCaml compilers, as well as the following commands: diff, dos2unix, sed

REM directory containing z3_api.h
set Z3SRC=%1

REM directory containing z3.dll and z3.lib
set Z3BIN=%2

REM directory containing debug z3.dll
set Z3BINDBG=%3

set PATH=.;%2;%3;%PATH%

echo Build test_capi
cl /nologo /I %Z3SRC% %Z3BIN%\z3.lib ..\test_capi\test_capi.c

echo Build test_mlapi
ocamlc -w -a -o test_mlapi.byte.exe z3.cma test_mlapi.ml
ocamlopt -w -a -o test_mlapi.exe z3.cmxa test_mlapi.ml
ocamlc -g -w -a -o test_mlapi.byte.dbg.exe z3_dbg.cma test_mlapi.ml
ocamlopt -g -w -a -o test_mlapi.dbg.exe z3_dbg.cmxa test_mlapi.ml

echo Build test_mlapiV3
ocamlopt -g -w -a -o test_mlapiV3.dbg.exe z3_dbg.cmxa test_mlapiV3.ml

echo Build test_theory
ocamlopt -g -w -a -o test_theory.dbg.exe z3_dbg.cmxa test_theory.ml

echo Build queen
ocamlopt -g -w -a -o queen.exe z3_dbg.cmxa queen.ml

echo Execute test_capi, test_mlapi, test_mlapiV3 and queen
test_capi.exe >test_capi.out 2>test_capi.orig.err
test_mlapi.dbg.exe >test_mlapi.out 2>test_mlapi.orig.err
test_mlapiV3.dbg.exe >test_mlapiV3.out 2>test_mlapiV3.orig.err
queen.exe >queen.out 2>queen.orig.err

REM Strip pointers as they will always differ
sed <test_capi.orig.err >test_capi.err "s/ \[.*\]/ [...]/g"
sed <test_mlapi.orig.err >test_mlapi.err "s/ \[.*\]/ [...]/g"
sed <test_mlapiV3.orig.err >test_mlapiV3.err "s/ \[.*\]/ [...]/g"
sed <queen.orig.err >queen.err "s/ \[.*\]/ [...]/g"
del test_capi.orig.err test_mlapi.orig.err test_mlapiV3.orig.err queen.orig.err

REM Compare with regressions
dos2unix *.out *.err 2>NUL
diff test_capi.regress.out test_capi.out >NUL || echo Regression failed, see: diff test_capi.regress.out test_capi.out
diff test_mlapi.regress.out test_mlapi.out >NUL || echo Regression failed, see: diff test_mlapi.regress.out test_mlapi.out
diff test_mlapiV3.regress.out test_mlapiV3.out >NUL || echo Regression failed, see: diff test_mlapiV3.regress.out test_mlapiV3.out
diff test_capi.regress.err test_capi.err >NUL || echo Regression failed, see: diff test_capi.regress.err test_capi.err
diff test_mlapi.regress.err test_mlapi.err >NUL || echo Regression failed, see: diff test_mlapi.regress.err test_mlapi.err
diff test_mlapiV3.regress.err test_mlapiV3.err >NUL || echo Regression failed, see: diff test_mlapiV3.regress.err test_mlapiV3.err
diff queen.regress.out queen.out >NUL || echo Regression failed, see: diff queen.regress.out queen.out
diff queen.regress.err queen.err >NUL || echo Regression failed, see: diff queen.regress.err queen.err

ENDLOCAL
