#!/bin/bash
# Usage: run.sh [path/to/z3]
# Runs insertion_sort.smt2 with smt.qi.update_generation=false and =true and
# checks that only the former proves the query within the file's rlimit.
Z3=${1:-z3}
DIR=$(cd "$(dirname "$0")" && pwd)
F="$DIR/insertion_sort.smt2"
rc=0
for setting in false:unsat true:unknown; do
  g=${setting%%:*}; want=${setting#*:}
  out=$("$Z3" -st smt.qi.update_generation=$g "$F" 2>&1)
  got=$(echo "$out" | head -1)
  stats=$(echo "$out" | grep -oE ':(rlimit-count|quant-instantiations) +[0-9]+' | tr -s ' ' | tr '\n' ' ')
  printf 'qi.update_generation=%-5s  %-7s (expected %-7s)  %s\n' "$g" "$got" "$want" "$stats"
  [ "$got" = "$want" ] || rc=1
done
exit $rc
