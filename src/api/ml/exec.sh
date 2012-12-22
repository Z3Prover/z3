#!/bin/sh
export LD_LIBRARY_PATH=../../lib:$LD_LIBRARY_PATH	# for linux
export DYLD_LIBRARY_PATH=../../lib:$DYLD_LIBRARY_PATH	# for osx
./test_mlapi
