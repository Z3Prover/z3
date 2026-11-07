# F* audit: PR 11585 (head 4a53e6b8786dc3ef4749c8e0e370885388ca7049, base 4ef6ad78b653c1b318a40a1c364abec01cf9f726)

PR open at that head, no prior `fstar-nfv-audit:<sha>` comment. Tools: F* 2026.09.27, pinned Z3 4.13.3 (independent backend).

## Scope (partial)
Audited function: `context::is_min_max_of_sums` in src/opt/opt_context.cpp (head lines ~1721-1830; head file sha256 3ad24dd268d390d97018f9ede23dd8eaa65cd6095049b3b1541abe4103b5d4e5, base sha256 b7d12fe66c601e505bd5f57b9733e135d23b913a1cbb0c14163cc92785c1c821).
Excluded (not audited): `simplify_fmls` model-converter composition change (line ~1651, `concat(m_model_converter, r->mc())`; only reviewed by inspection: concat returns the non-null one if either is null and normalize() resets m_model_converter first, line 1266); sort-preserving numerals (`mk_numeral(1/0, term->get_sort())`), `mk_ge(c, mk_int(k))` int/real coercion for Real `c`, the new `mark.is_marked(y)` self-reference guard (inspected only), src/test/opt_bounds.cpp (tests; not executed), and all C++ memory/AST plumbing.

## Intended property and assumptions
Let c_1..c_m be the sums collected in `cardinalities`, each a sum of 0/1 ite terms with value in [0, len_i]. min case: min x s.t. x >= c_i; encoding p_k (k=1..N) with c_i>=k => p_k, x = sum p_k, minimize sum, N = max_cardinality. max case: p_k => c_i>=k, N = min_cardinality.
Assumptions (manually reviewed): c_i <= len_i (sum of 0/1 terms); max c <= max len = N (min); min c <= min len = N (max, take the i with minimal length); fresh p_k, original term not occurring in the c_i (checked by the new mark guard); optimizer is exact on the rewritten objective.

## Obligations (module Z3OptIteSumPr11585.fst, all verified)
1. O1 (min, proved): canonical p_k=(k<=max c) is feasible with sum = max c; every feasible p has sum >= max c (the fixed optimum equals max_i c_i).
2. O2 (max, proved): canonical p_k=(k<=min c) feasible with sum = min c; every feasible p has sum <= min c.
3. O4 (proved): in min case, x = sum p_k >= every c_i, i.e. the added equality `x = sum` preserves the original bounds (the issue 11581 failure mode: base used `x` instead of the bound sums and min_cardinality thresholds, undercounting).
Additional lemma sum01_le_len supports the range assumption. No counterexample was found for the head semantics. Base behavior (cardinalities.push_back(x), thresholds up to min_cardinality, no x=sum) is consistent with the issue's reported wrong minimum but was not separately mechanized.

## Correspondence
F* `count p n` = number of true p_k among 1..N = `sum` of ite(p_k,1,0). `feas_min`/`feas_max` = the generated implications. Lists of nat model the integer values of c_i. This is a semantic model, not verification of C++ execution, Z3 arithmetic coercion, soft-constraint handling, or model reconstruction. Inherited trust: F* standard library (FStar.List.Tot, FStar.Classical) and the Z3 4.13.3 backend.

## Reproduce
fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out Z3OptIteSumPr11585.fst   (fresh dirs, 120 s timeout; exit 0)
