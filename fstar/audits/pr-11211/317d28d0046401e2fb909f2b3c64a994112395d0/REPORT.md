# F* audit of PR #11211 at 317d28d0046401e2fb909f2b3c64a994112395d0

Partial scope (one function, one obligation). Previously audited heads ef62c14 and 02eb8bb covered arith_swine.cpp.

## Obligation N (proved)
`arith_rewriter::mk_power_core`, Int branch (arith_rewriter.cpp ~L2028-2047 at head; file sha256 9980c4e3...6cd1): rewrite `(x**y)**z -> x**(ite (y<0 && z<0) (-(y*z)) (y*z))`.
Property: under Z3 integer power semantics (negative exponent gives 0 except base +/-1), `zpow (zpow b y) z == zpow b (if y<0 && z<0 then -(y*z) else y*z)` for all integers b,y,z. Proved in `SwineAudit3.fst` (`nested_valid`); no counterexample exists.

## Correspondence / assumptions
`pow` models compute_power for exponent>=0; `zpow` models the negative-exponent semantics from the Int branch of mk_power_core (this PR's own negative-exponent rewrite, taken as the spec). Unbounded integers are used; m_max_degree guards only restrict folding. No base-module imports beyond FStar.Math.Lemmas; no admit/assume.

## Exclusions
All other changed functions: reduce_power, real-sort branch of mk_power_core (y=0 -> 1 reorder, ensure_real removal), mk_mul_core, nla_powers.cpp, arith_axioms.cpp mk_power_axiom, purify_arith_tactic, arith_decl_plugin OP_POWER sort checks, theory_lra/sat/smt files, tests, and all C++ plumbing/memory safety. Not mechanized C++ verification.

## Reproduce
fstar.exe --smt z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir c --odir o SwineAudit3.fst
