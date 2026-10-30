# F* audit PR #11436 @ ca284770

Source: fstar/Z3Tptp.fst at head ca284770b99770aaf06e8fb5dd8a4ea64edf8491 (base c95b61cb), sha256 72fe06485aa590a8586c515701a2185de4764d8506068fd61117b83940a9f5a8, 477 lines. Functions: true_atom/same_atom, same_literals, equality_reduction. The exporter is documented as presentation only (not a proof-checking rule).

## Obligations (all proved)
1. same_atom_sound: same_atom a b implies equal truth under every interpretation.
2. same_literals_sound: mutual containment modulo same_atom preserves clause truth.
3. equality_reduction_sound: dropping negative reflexive equalities preserves clause truth.

## Correspondence / assumptions
Z3TptpModel.fst is a hand-written abstraction (terms as nats, equality as equality of denotations), not extracted from Z3Tptp.fst. The eq/oeq interp check is abstracted to one equality kind; Bool-sorted equalities are not modelled (source excludes them). Only the F* standard library is trusted; no admit/assume.

## Exclusions
All other functions in Z3Tptp.fst (visit, rewrites, quantified_instance, naming, typing), Z3Cherry.fst change, OCaml/Cherry runtimes, convert_taelja.py, tests, build scripts. Not mechanized verification of C++/OCaml execution, memory safety, or exporter output validity.

## Reproduce
fstar.exe --smt z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out Z3TptpModel.fst (F* 2026.09.27, Z3 4.13.3).