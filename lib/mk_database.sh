#!/bin/sh
dos2unix database.smt
./gen database.smt | awk 'BEGIN { print "char const * g_pattern_database =" } { print "\"" $0 "\\n\"" } END { print ";" }' > database.h
