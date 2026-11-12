# F* audit PR #11636 @ 2202fc729afaf3796ed115dbf155ac3a3be5d490 (base 8927ff98ea8eae56021f8e8ea874a9465ea6a257)

Sources: src/opt/opt_context.cpp, head sha256 of decoded file b8e0493a7b36..., base 3ad24dd268d3...; lines 1706-1830 at head (simplify_min_max_of_sums, is_min_max_of_sums).

## Change
The rewrite min/max x with x<=/>= sums of ite(c,0/1) into threshold soft constraints (x = sum ite(p_k,1,0)) is now skipped when (a) recfun::util(m).has_rec_defs() and (b) the objective term is not an uninterpreted constant (previously is_uninterp allowed e.g. f(0)).

## Intended property
The rewrite must not change satisfiability/optimum. Environment assumption: if the objective is an uninterpreted constant and no recursive definitions exist, every constraint mentioning it occurs syntactically in fmls (mark_occurs), so the non-marked formulas do not constrain it.

## Obligations (OptIteBoundAudit.fst)
1. proved (witness on base guard): o1_original_sat / o1_rewritten_unsat: a hidden constraint x=5 (via read_x(0)=5 or f(t)=5 with t=0 aliasing f(0)) is satisfiable originally with x>=ite(a,1,0), but unsatisfiable after the rewrite x=ite(p,1,0). This confirms the base bug mechanism is real in the model; the C++ reachability is supported by the PR regression tests, not mechanized here.
2. proved: o2_guard_blocks_witness: the new guard (not has_rec_defs && is_uninterp_const) rejects both witness patterns (rec-def case, and f(0) non-constant case) and still admits the plain-constant case.
3. proved: o3_lower / o3_attained: for the admitted fragment (closed constant objective, two bounds with values in [0,2], thresholds k=1,2), the threshold encoding has minimum sum exactly max(c1,c2), i.e. the rewrite preserves the optimum.

## Mapping and limits
F* abstracts the C++ AST as integers/booleans; b2i models ite(p,1,0); feas models the generated implications. Manually reviewed only: mark_occurs/expr_mark plumbing, fmls mutation, memory safety, whole-solver behaviour. Residual risk: has_rec_defs() is a global over-approximation (safe, only loses optimization); other hidden dependencies that are not recdefs (e.g. other theory plugins, model-based definitions) are not covered.

## Excluded
src/test/opt_bounds.cpp test changes (not semantic), include addition, other functions in opt_context.cpp.

## Versions
F* 2026.09.27; Z3 4.13.3 (pinned release backend).

## Reproduce
/tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include /home/runner/work/z3/z3/fstar --z3rlimit 10 --cache_dir cache --odir out OptIteBoundAudit.fst
