@echo off

REM Script to generate the Z3 OCaml API
REM
REM Assumes that environment variables are set to provide access to the following commands: camlidl, dos2unix, grep, sed, unix2dos
REM
REM Invoke with "-D UNSAFE_ERRORS" to build version that does not support recoverable errors, but avoids some error-checking overhead.
REM Invoke with "-D LEAK_CONTEXTS" to build version that leaks Z3_context objects, but avoids some garbage-collection overhead.

REM ../lib/z3_api.h -> z3V3_api.idl using add_error_checking.V3.sed and build.sed
sed -f add_error_checking.V3.sed ../lib/z3_api.h | sed -f build.sed >z3V3_api.idl
if errorlevel 1 goto :EOF

REM z3.idl -> z3V3_stubs.c, z3V3.mli, z3V3.ml
camlidl -D MLAPIV3 %* z3.idl
move >NUL z3_stubs.c z3V3_stubs.c
move >NUL z3.ml z3V3.ml
move >NUL z3.mli z3V3.mli
if errorlevel 1 goto :EOF

REM ../lib/z3_api.h -> z3_api.idl
REM add calls to error checking routine
REM convert from doxygen to ocamldoc markup and other syntactic munging
sed <../lib/z3_api.h -f add_error_checking.sed | ^
sed -f build.sed >z3_api.idl
if errorlevel 1 goto :EOF

REM z3.idl -> z3_stubs.c, z3.mli, z3.ml
camlidl %* z3.idl
if errorlevel 1 goto :EOF

REM sometimes z3_stubs.c can be generated with mixed line endings, which can confuse sed and grep
dos2unix 2>NUL z3V3_stubs.c ; unix2dos 2>NUL z3V3_stubs.c
dos2unix 2>NUL z3_stubs.c ; unix2dos 2>NUL z3_stubs.c

REM modify generated z3.ml{,i} to remove "Z3_" prefix from names
move >NUL z3V3.mli z3V3.1.mli && sed "s/{\!Z3\./{!/g;s/\<[zZ]3_//g" z3V3.1.mli >z3V3.mli && del z3V3.1.mli
move >NUL z3V3.ml z3V3.1.ml && sed "s/{\!Z3\./{!/g;s/\<[zZ]3_//g" z3V3.1.ml >z3V3.ml && del z3V3.1.ml
move >NUL z3.mli z3.1.mli && sed "s/{\!Z3\./{!/g;s/\<[zZ]3_//g" z3.1.mli >z3.mli && del z3.1.mli
move >NUL z3.ml z3.1.ml && sed "s/{\!Z3\./{!/g;s/\<[zZ]3_//g" z3.1.ml >z3.ml && del z3.1.ml

REM modify generated z3V3 files to rename z3_ to z3V3_
move >NUL z3V3.mli z3V3.2.mli && sed "s/camlidl\(.*\)_z3_/camlidl\1_z3V3_/g" z3V3.2.mli >z3V3.mli && del z3V3.2.mli
move >NUL z3V3.ml z3V3.2.ml && sed "s/camlidl\(.*\)_z3_/camlidl\1_z3V3_/g" z3V3.2.ml >z3V3.ml && del z3V3.2.ml
move >NUL z3V3_stubs.c z3V3_stubs.2.c && sed "s/camlidl\(.*\)_z3_/camlidl\1_z3V3_/g" z3V3_stubs.2.c >z3V3_stubs.c && del z3V3_stubs.2.c


REM substitute out type equations for enums and options
REM reverse order of substitution of enums to avoid matching prefixes such as enum_1 of enum_10
grep "^and \([a-z][a-zA-Z_]*\) = \([a-z][a-zA-Z_]*[0-9]*\)$" z3.mli | sed "s|and \([a-zA-Z_]*\) = \([ a-zA-Z_0-9]*\)|s/\2/\1/g|g" | sed "1!G;h;$!d" >rename.sed
grep "^and \([a-z][a-zA-Z_]*\) = \([a-z][a-zA-Z_]* option*\)$" z3.mli | sed "s|and \([a-zA-Z_]*\) = \([ a-zA-Z_0-9]*\)|s/\1/\2/g|g" >>rename.sed
move >NUL z3.mli z3.3.mli && sed -f rename.sed z3.3.mli >z3.mli && del z3.3.mli
move >NUL z3.ml z3.3.ml && sed -f rename.sed z3.3.ml >z3.ml && del z3.3.ml
del rename.sed

grep "^and \([a-z][a-zA-Z_]*\) = \([a-z][a-zA-Z_]*[0-9]*\)$" z3V3.mli | sed "s|and \([a-zA-Z_]*\) = \([ a-zA-Z_0-9]*\)|s/\2/\1/g|g" | sed "1!G;h;$!d" >rename.sed
grep "^and \([a-z][a-zA-Z_]*\) = \([a-z][a-zA-Z_]* option*\)$" z3V3.mli | sed "s|and \([a-zA-Z_]*\) = \([ a-zA-Z_0-9]*\)|s/\1/\2/g|g" >>rename.sed
move >NUL z3V3.mli z3V3.3.mli && sed -f rename.sed z3V3.3.mli >z3V3.mli && del z3V3.3.mli
move >NUL z3V3.ml z3V3.3.ml && sed -f rename.sed z3V3.3.ml >z3V3.ml && del z3V3.3.ml
del rename.sed

REM remove cyclic definitions introduced by substituting type equations
move >NUL z3V3.mli z3V3.4.mli && sed "s/^and \([a-z][a-zA-Z_ ]*\) = \1$//g" z3V3.4.mli >z3V3.mli && del z3V3.4.mli
move >NUL z3V3.ml z3V3.4.ml && sed "s/^and \([a-z][a-zA-Z_ ]*\) = \1$//g" z3V3.4.ml >z3V3.ml && del z3V3.4.ml
move >NUL z3.mli z3.4.mli && sed "s/^and \([a-z][a-zA-Z_ ]*\) = \1$//g" z3.4.mli >z3.mli && del z3.4.mli
move >NUL z3.ml z3.4.ml && sed "s/^and \([a-z][a-zA-Z_ ]*\) = \1$//g" z3.4.ml >z3.ml && del z3.4.ml

REM append Z3.V3 module onto Z3 module
type z3V3.ml >> z3.ml
type z3V3.mli >> z3.mli
sed "1,22d" z3V3_stubs.c >> z3_stubs.c
del /q 2>NUL z3V3_api.idl z3V3.ml z3V3.mli z3V3_stubs.c
