#!/bin/bash

# Script to generate the Z3 OCaml API
#
# Assumes that environment variables are set to provide access to the following commands: camlidl, gcc, grep, sed
#
# This script uses 'gcc -E' as the C preprocessor, other C preprocessors may work but have not been tested.
#
# Invoke with "-DUNSAFE_ERRORS" to build version that does not support recoverable errors, but avoids some error-checking overhead.
# Invoke with "-DLEAK_CONTEXTS" to build version that leaks Z3_context objects, but avoids some garbage-collection overhead.


# add calls to error checking routine
# convert from doxygen to ocamldoc markup and other syntactic munging
# ../z3_api.h -> z3V3_api.idl
sed -f add_error_checking.V3.sed -f preprocess.sed ../z3_api.h > z3V3_api.idl

# z3.idl (z3V3_api.idl x3V3.mli x3V3.ml) -> z3V3_stubs.c, z3V3.mli, z3V3.ml
gcc -E -w -P -CC -xc -DCAMLIDL -DMLAPIV3 $@ z3.0.idl > z3V3.idl
camlidl -nocpp z3V3.idl

# reverse.sed to reverse order of substitution of enums to avoid matching prefixes such as enum_1 of enum_10
grep "^and z3_[a-zA-Z0-9_]* = [a-z][a-zA-Z0-9_]*$"         z3V3.mli | sed -e "s|and z3_\([a-zA-Z0-9_]*\) = \([a-zA-Z0-9_]*\)|s/\2/\1/g|g" -f reverse.sed > /tmp/renameV3.sed
grep "^and z3_[a-zA-Z0-9_]* = [a-z][a-zA-Z0-9_ ]* option$" z3V3.mli | sed -e "s|and \(z3_[a-zA-Z0-9_]*\) = \([a-zA-Z0-9_ ]*\)|s/\1/\2/g|g"              >> /tmp/renameV3.sed

# rename.sed to substitute out type equations for enums and options, then postprocess
cp -f z3V3.mli z3V3.ml /tmp
sed -f /tmp/renameV3.sed -f postprocess.sed /tmp/z3V3.mli > z3V3.mli
sed -f /tmp/renameV3.sed -f postprocess.sed /tmp/z3V3.ml  > z3V3.ml

# ../z3_api.h -> z3_api.idl
sed -f add_error_checking.sed -f preprocess.sed ../z3_api.h > z3_api.idl

# z3.idl (z3_api.idl x3.ml) -> z3_stubs.c, z3.mli, z3.ml
gcc -E -w -P -CC -xc -I. -DCAMLIDL $@ z3.0.idl > z3.idl
camlidl -nocpp z3.idl

# reverse.sed to reverse order of substitution of enums to avoid matching prefixes such as enum_1 of enum_10
grep "^and z3_[a-zA-Z0-9_]* = [a-z][a-zA-Z0-9_]*$"         z3.mli | sed -e "s|and z3_\([a-zA-Z0-9_]*\) = \([a-zA-Z0-9_]*\)|s/\2/\1/g|g" -f reverse.sed > /tmp/rename.sed
grep "^and z3_[a-zA-Z0-9_]* = [a-z][a-zA-Z0-9_ ]* option$" z3.mli | sed -e "s|and \(z3_[a-zA-Z0-9_]*\) = \([a-zA-Z0-9_ ]*\)|s/\1/\2/g|g"              >> /tmp/rename.sed

# rename.sed to substitute out type equations for enums and options, then postprocess
cp z3.mli z3.ml /tmp
sed -f /tmp/rename.sed -f postprocess.sed /tmp/z3.mli > z3.mli
sed -f /tmp/rename.sed -f postprocess.sed /tmp/z3.ml > z3.ml


# append Z3.V3 module onto Z3 module
cat z3V3.mli >> z3.mli
cat z3V3.ml >> z3.ml
sed "1,22d" z3V3_stubs.c >> z3_stubs.c

rm -f z3V3_api.idl z3V3.idl z3V3.ml z3V3.mli z3V3_stubs.c z3_api.idl z3.idl
