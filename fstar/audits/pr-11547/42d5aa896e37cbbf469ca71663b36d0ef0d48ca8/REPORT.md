# F* audit of PR 11547 at 42d5aa896e37cbbf469ca71663b36d0ef0d48ca8 (base 684853cb)
Incremental over previously audited head 9ce70d88. Tools: F* 2026.09.27, Z3 4.13.3 (pinned release backend).

## Changed behavior (partial scope: 3 functions)
1. par_and_then_tactical::operator() (src/tactic/tactical.cpp): sequential proof fallback replaced by `use_seq=false` (dead branch) + `fail_if_proof_generation("par_and_then", in)`; proof mode now throws.
2. smt_tactic l_false case (smt_tactic_core.cpp ~L253): proof mode with missing/non-false proof now throws instead of returning input unchanged.
3. Per-tactic guard migration (representative: occf/nlsat/qsat/parallel_tactic): `if proofs_enabled -> return input` replaced by fail_if_proof_generation (throws).

## Obligations (all proved)
O1 par_then throws in proof mode; O2 unchanged without proofs; O3 the old return-of-input is no longer produced; O4 smt l_false without false proof throws; O5 otherwise continues; O6 fail_if_proof throws in proof mode.

## Assumptions
fail_if_proof_generation(g) throws iff g.proofs_enabled() (declaration in tactic.h verified; definition in tactic.cpp not re-read at this head, taken from base semantics). Goals abstracted to (proofs,id).

## Observations (not counterexamples)
- tactical.cpp now has dead code `bool use_seq; use_seq=false; if(use_seq){...}`: the sequential fallback is unreachable; in proof mode par_then now throws rather than falling back. This is a behavioral change from 9ce70d88 (previously sequential), soundness-safe but a usability regression for proof-mode users of par_then.
- qsat qe_rec wraps in simplify under proof probe; not modeled.

## Exclusions
Remaining ~50 per-tactic edits, src/test/smt_context.cpp, mk_qe_rec_tactic cond/and_then, ackermannize, sls, etc. C++ execution, memory safety, exception handling by callers not verified.

## Reproduce
fstar.exe --smt z3-4.13.3 --z3version 4.13.3 --include fstar --cache_dir c --odir o --z3rlimit 10 Z3PR11547Throw.fst