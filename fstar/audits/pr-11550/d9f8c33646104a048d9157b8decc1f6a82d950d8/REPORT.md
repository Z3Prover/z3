# F* audit, PR #11550 @ d9f8c33646104a048d9157b8decc1f6a82d950d8 (base c79e8787949d31c3559371ba307f2dda2d2b3018)

Scope (partial): one changed production function, `seq::eq_solver::is_var` in `src/ast/seq/seq_eq_solver.cpp` (PR deletes `!seq.str.is_nth_i(a) &&`, line ~441 in base). sha256 base file c70fa1a8a313afaad077da100103c58e2594e718919232f72d48de9649f7fff7, head 424c573447f4b00958b9e91d9fbe4a8bfb7cadabdf71c79088ebfbce92a9549a.
Excluded: `src/test/seq_rewriter.cpp` (tests, not audited), the model builder / seq_model / theory_seq length handling that consumes the change, and the claimed fix of issue #11544 end to end (not mechanized).

## Obligations (all **proved**; no counterexample searched for beyond this model)
- O1: new `is_var` differs from old exactly on `nth_i` terms.
- O3: reduce_unit soundness for an nth_i term used as `x`: if `x` does not occur (via concat/unit/nth_i descent, as in `eq_solver::occurs`) in `t`, then installing `x := t` is consistent (x and t evaluate equal after override).
- O2: `branch_unit_variable`: X = units and |X| = k implies X = first k units (applies now to nth terms too).

## Correspondence / assumptions
Terms are an abstract datatype; `Nth` is a term-keyed value (congruence of seq.nth treated as handled by the E-graph). Only a subset of constructors is modelled (itos, map, foldl, ite omitted). `occurs` models the C++ one but `m.is_ite` conservatism is omitted. Not modelled: sort restriction (is_var requires seq sort so scalar nth is unaffected), interaction with the nth-solved rule `match_nth_solved_aux` (where an nth_i-as-variable could be a new case: `ls[0]` is a var and rs are units of nth_i of ls[0]), termination, model construction, memory safety. These remain manual review. Result is a semantic audit, not verification of C++.

## Reproduce
`/tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out Z3PR11550NthVar.fst` (F* 2026.09.27, Z3 4.13.3, fresh cache, exit 0, "All verification conditions discharged successfully").
