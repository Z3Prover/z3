# F* audit of PR 11665 @ 212c81d577fbb97d822aa3090c7101abe72b7324 (base 9e450b2e)

Scope (partial): one changed function, `recfun_rewriter::inc_unfold` (src/ast/rewriter/recfun_rewriter.cpp, new, lines ~31-48), four obligations.

Obligations (all PROVED in RecfunBudget.fst):
1. O1: counter invariant num <= max preserved; `true` charges exactly one unit and only when num < max; `false` leaves num unchanged; max unchanged.
2. O2: an application already in m_blocked is never unfolded.
3. O3: at num == max, a new application is refused, recorded in m_blocked, and later retries are refused at no cost.
4. O4: after reset_unfolds with empty blocked set, the first unfolding is allowed iff max > 0.

Correspondence: state record = (m_num_unfolds, m_max_unfolds, m_blocked); applications abstracted to nat ids (hash-consed AST pointer equality); `inc_unfold` mirrors the C++ branch order. No counterexample found; none claimed.

Assumptions: hash-consing makes `m_blocked.contains(a)` equal to id equality; mk_app returns the same pointer for equal f/args; m_pinned keeps blocked apps alive so pointers are not reused; m_max_unfolds initialised by updt_params in the constructor (manually read, not proved). Base: F* stdlib only, no base fstar modules imported.

Not mechanized: C++ execution, memory safety, obj_hashtable behaviour, whether BR_FAILED in th_rewriter/model_evaluator preserves soundness of the evaluator (model_evaluator.get_macro returning false for recursive functions with interp, the is_rec/BR_DONE path), reset_unfolds placement in th_rewriter entry points, completeness effects (blocked set never reset in th_rewriter, so leftover unfolds are skipped for its lifetime; incompleteness, not unsoundness, by inspection).

Excluded changes: th_rewriter.cpp reset_unfolds calls; model_evaluator.cpp get_macro/reduce_app/reset changes; rewriter_params.hpp; recfun_rewriter.h plumbing; src/test/smt_context.cpp; mk_app_core guard.

Versions: F* 2026.09.27, Z3 4.13.3 (pinned release backend). Source file sha256 9b4bcf78e560495aeec55eda857558d64c7ce44307fcc025fb859dd6b21b35b0.

Reproduce: fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out RecfunBudget.fst
