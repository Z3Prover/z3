# F* audit of PR #11559 (head 46bf1c4f47c1b27968a82fbbb3d36dd96d55d2fb, base 684853cb1545622a353660d5de601032f060ffb1)

fstar-nfv-audit:46bf1c4f47c1b27968a82fbbb3d36dd96d55d2fb

## Scope (partial)
Changed function audited: the `m_mode == qsat_qe` / `case l_false` branch of the qsat tactic operator() in `src/qe/qsat.cpp` (head lines 1333-1357; decoded head file sha256 d1507f58215e35fc7c960ed0d7af8c409061e7fa01feced9923802fe4a1e6b97). Only the shape of the re-quantification is covered.

Excluded (not audited): the two new regression tests in `src/test/mbp_qel.cpp` (tests, executed not proved); trailing blank-line removal; the pre-existing m_free_vars binding at ~lines 1110-1117; MBP/projection correctness; `occurs`; mk_forall/mk_exists de Bruijn abstraction; overall QE soundness and equivalence of result to input.

## Source behavior
After `mk_and(m_answer)`, for i = m_vars.size()-1 down to 1: collect vars of m_vars[i] still occurring in fml; if any, wrap with mk_forall when is_exists(i) (even level) else mk_exists. Level 0 is untouched. Then remaining m_free_vars that occur are existentially bound. In qe mode the input goes through push_not before hoist, so level parity is dual to input polarity; the loop therefore uses the dual quantifier, restoring input-side polarity (level 1 -> exists).

## Obligations (Z3QsatRequantPrefix.fst) - all proved
- O1 wrap_eq: the loop n-1..1 (each new wrapper outermost) yields exactly levels 1..n-1 in increasing order (outermost = level 1), i.e. original nesting order.
- O2: level 1 gets Ex.
- O3: adjacent levels get opposite quantifiers (alternation preserved).
- O4: concrete n=4 gives [(1,Ex);(2,All);(3,Ex)].

## Correspondence and assumptions
`dual_of_is_exists` models `is_exists(i) ? mk_forall : mk_exists`; `wrap` models the loop; lists model nested quantifier blocks. Assumed, manually reviewed, not mechanized: m_vars follows alternating hoist structure with level 0 free; skipping non-occurring variables/empty blocks preserves relative order; mk_forall/mk_exists bind the given constants; vars bound in the loop no longer occur free, so the m_free_vars pass does not double-bind; m_free_vars (projected vars from project_qe/project) are not also in m_vars[i>=1] in a way that matters. No refutation witness was constructed; none found. Only FStar.List.Tot from the standard library is used; no base fstar modules imported; no admit/assume. This is not mechanized verification of C++ execution, memory safety, AST plumbing, or the whole solver.

## Reproduce
In a fresh dir with fresh cache/out: timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --include (checkout)/fstar --cache_dir cache --odir out Z3QsatRequantPrefix.fst