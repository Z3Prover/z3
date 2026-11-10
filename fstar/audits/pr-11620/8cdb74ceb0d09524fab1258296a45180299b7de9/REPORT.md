# F* audit PR #11620 @ 8cdb74ceb0d09524fab1258296a45180299b7de9 (base 532cbc4aee06a3745a318fc9e8b86124123c7bca)

Scope (partial): 1 changed function, src/model/model_evaluator.cpp evaluator_cfg::reduce_app Boolean-family branch, ~lines 284-292 at head (head.cpp sha256 86188fdd44fda8d0aa9d57e43f856137f988f52ee8bd89a2065fc6c103c517ec).
Change: after m_b_rw.mk_app_core, if k==OP_ITE && st<BR_DONE return BR_REWRITE1.
Excluded: src/test/model_evaluator.cpp (regression tests, not executed); rewriter engine semantics of BR_REWRITE1 (rewriter_tpl/rewriter.cpp); arithmetic rewriter div/mod/rem handling; model completion; quantifier cases.

Obligations (module Pr11620Clamp.fst, enum order from rewriter_types.h):
1. PROVED: non-ITE and DONE/FAILED statuses are unchanged.
2. PROVED: clamp never increases status depth; any ITE rewrite request becomes BR_REWRITE1.
3. PROVED: result term is not altered by the wrapper (status-only change).
4. PROVED (witness): ITE with BR_REWRITE_FULL is now downgraded to BR_REWRITE1, i.e. deeper re-rewriting is intentionally skipped. No counterexample to the stated property was sought/established.

Not established: the main intent (no non-termination for ite(z>0, div 4 (1+z), 0) with div0=0) and soundness/value-equivalence of the result when the downgraded REWRITE_FULL/2/3 rewrites are cut short (result might be left less simplified; correctness is preserved only if every builtin rewrite result is already semantically equal, which is manual review). Termination needs a model of the rewriter's re-visit mechanics, which was not formalized. Therefore verdict is inconclusive, not a safety claim.

Mapping: br_status modeled as an ordered enum; the code's `st < BR_DONE` uses enum integer order. Assumptions: m_b_rw.mk_app_core returns an arbitrary status/result; no assumptions beyond F* standard library/Z3 4.13.3 (F* 2026.09.27). Not mechanized: C++ execution, memory safety, rewriter engine.

Reproduce: cd fstar-audit; mkdir cache out; /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out Pr11620Clamp.fst
