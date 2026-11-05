# F* audit PR 11452 @ a2952e5e10fc0603aa04ffac37048506bf6cb72f

Delta base: 976ed9e494b756fa5412b273272f517fc79a221e (previously audited). Head sources fetched via the contents API: src/opt/opt_nlsat.cpp sha256 022a7bbde788df36a918dcb5ae9f200fa4880686f45b712da3d9adb908b99066; src/opt/optsmt.cpp sha256 2e36fbe89ee478efb5fde88c6f533f721938cb20c327008d710b8411ae41f25a; src/test/opt_nlsat.cpp sha256 7fe21d54236ce1dd37c2b57f92b9fa8b0c1c0a4c793b4d59a7b5992d0eb6f318.

## Changed function
`nlsat_opt::can_approach_from_below(hard,obj,lo,bound,budget)`: the public wrapper was removed from opt_nlsat.cpp (about L194) and opt_nlsat.h. Its production path was certify_result (opt_nlsat.cpp about L515), which already called the private overload through bounded_limit_query(m, supremum_rlimit, ...), so budget handling is unchanged.

## Obligations (all proved)
- O1: the new query returns only the nlsat result r or l_undef.
- O2: if the removed wrapper's outer guards (is_real obj, in_nra_fragment(hard,obj,true)) held, old and new results coincide.
- O3: old and new differ only if the old outer guard failed (old = l_undef); any definite new answer still requires the inner guard in check_limit (in_nra_fragment(purified goal, T, reals_only=true), about L225).

## Correspondence and assumptions
Booleans abstract the guard conditions; r abstracts the nlsat s.check_limit result. Assumed by manual review, not mechanized: the inner guard rejects integer-sorted T and integer variables, and maximize's own in_nra_fragment check precedes certify_result. Not verified: C++ execution, lambda and rlimit scope handling, memory safety, tests.

## Exclusions
Rewritten tests in src/test/opt_nlsat.cpp, curve certificate, optsmt integration, prove_unbounded, in_nra_fragment internals.

## Reproduce
fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out Z3OptNlsatInline.fst

F* 2026.09.27; Z3 4.13.3; no base modules imported (standard library only).
