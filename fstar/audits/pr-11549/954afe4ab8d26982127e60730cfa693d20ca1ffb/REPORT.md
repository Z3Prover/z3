# F* audit PR #11549 @ 954afe4ab8d26982127e60730cfa693d20ca1ffb (base c79e8787949d31c3559371ba307f2dda2d2b3018)

Source: src/smt/seq_eq_solver.cpp `@head`, lines 1198-1245 (solve_nth_eq); file sha256 8388782771ff2f65023b913e538b4c34e185ae4a6ea17bf7f0f4238e189df20f (fetched via contents API, saved under /tmp/gh-aw/agent/src).

## Property
nth_i(s,idx)=rhs decomposes s = pre(s,idx) ++ unit(rhs) ++ post(s,idx+1) only when 0<=idx(len(s) is established (asserted true in the SAT context), with those bound literals joined into the dependency; otherwise only the equation on the nth_i term is solved (add_solution).

## Obligations (all proved)
- O1: for 0<=i<len s, s = pre s i ++ [nth_i s i d] ++ post s (i+1) (soundness of guarded decomposition).
- O2: pre s 0 = [] (justifies omitting mk_pre when idx is numeral 0).
- O3: witness s=[], idx=0: guards fail and the unguarded decomposition is false, i.e. why the guard is needed (explains issue #11545 pre-fix behaviour; proved as a fact about the model, not a claim about the PR head).

## Mapping / assumptions
Sequences=F* lists; nth_i out-of-range = unconstrained value d; pre/post=splitAt. Guard checks (ctx.get_assignment == l_true) are modelled as the precondition. Assumes dependency joins (mk_leaf(assumption(lit))) correctly record the literals as justification, that mk_literal/get_assignment behave as named, and that the idx_ge_0 != true_literal check is just an optimization: reviewed manually, NOT mechanized. Not verified: C++ execution, memory safety, the m_nth_eq2_cache logic, add_solution fallback completeness (the else branch solves ls[0]=rhs which is a sound equation by itself), termination/incompleteness interplay, the whole solver. Base modules not imported; only FStar.List.Tot standard library.

## Exclusions
src/test/seq_rewriter.cpp regression test (not formalized; not executed).

## Reproduce
fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out NthEqGuard.fst
F* 2026.09.27, Z3 4.13.3.