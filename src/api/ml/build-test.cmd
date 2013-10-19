@echo off

if not exist ..\..\ocaml\z3.cmxa (
        echo "YOU MUST BUILD OCAML API! Go to directory ..\ocaml"
        goto :EOF
)

REM ocaml (>= 3.11) calls the linker through flexlink
ocamlc -version >> ocaml_version
set /p OCAML_VERSION= <ocaml_version
if %OCAML_VERSION% GEQ 3.11 (
    set XCFLAGS=
) else (
    set XCFLAGS=/nologo /MT /DWIN32
)

ocamlc -w A -ccopt "%XCFLAGS%" -o test_mlapi_byte.exe -I ..\..\ocaml z3.cma test_mlapi.ml

ocamlopt -w A -ccopt "%XCFLAGS%" -o test_mlapi.exe -I ..\..\ocaml z3.cmxa test_mlapi.ml
