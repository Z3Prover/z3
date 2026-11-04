# F* audit of PR #11531 at f09f37af864aa03801c4fe4fb2631c9445b20424 (incremental)
Scope: partial. Base for comparison: previously audited head 6c2ed83b7dcff99212836a62af3483a7369efec3 (already audited: proved). The only change since is src/ast/substitution/demodulator_rewriter.cpp, demodulator_match_subst::match_args (~lines 969-980): `for_each_expr(proc, arg)` became `for_each_expr(proc, visited, arg)` with a fresh `expr_mark visited` (DAG-visit-once instead of per-path). Head file sha256 (as fetched via contents API) df29c9f81b6a5c6728ecdc17d90ec4ad992a7ffac22c11030e63e1f73ee4dd42.
## Obligations (all proved)
1. visit_idem: re-visiting a node by match_args_aux_proc is a no-op after a successful visit.
2. run_preserves/visit_preserves: visits never rebind an existing variable binding.
3. dup_ok: dropping a repeated visit of an already-visited non-quantifier node does not change the traversal result (success/failure and final substitution), so visit-once is equivalent to visit-per-path.
## Correspondence
Nodes: V k = var, Q = quantifier (throws no_match), A = other app (no-op). Substitution maps var -> self (expr_offset(n,1)) or other. Traversal order is modelled as a list; the model's dedup is that of expr_mark. Quantifier nodes always fail, so skipping a repeat of a quantifier is also safe because the first visit already threw.
## Assumptions / not mechanized
for_each_expr(proc, visited, e) semantics (marks and skips visited nodes, visits all reachable nodes once) is read manually; the shared `visited` across the loop over lhs args is also sound by the same argument. C++ execution, memory safety, and the rest of the PR are excluded. Only this one changed function was audited; the earlier head's obligations are not re-proved. No admit/assume used. Base modules not imported.
## Reproduce
fstar.exe --smt z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir c --odir o Z3DemodVisited.fst (F* 2026.09.27, Z3 4.13.3)
