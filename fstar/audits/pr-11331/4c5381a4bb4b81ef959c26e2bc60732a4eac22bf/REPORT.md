## Scope
Head 4c5381a4bb4b81ef959c26e2bc60732a4eac22bf (base a2fae73358e4a928da63d1c131e9fe2bbac8c855). Audited function: theory_seq::new_eq_eh (src/smt/theory_seq.cpp ~L3447-3451): replaces `m_new_solution = true` with `solve_eqs(m_eqs.size()-1)`.

## Obligations (all proved)
- O1 eager: when m.inc() polls true, a solvable new equation is erased and state is unchanged (restores base behaviour).
- O2 interrupt: when polling fails at once, the equation is retained, prior equations are kept, and m_new_solution is raised (via the PR's post-loop `if (i < m_eqs.size()) m_new_solution = true`).
- O3 no unsound sat: if interrupted or unsolved, m_eqs stays non-empty so the FC_DONE gate (m_eqs empty) is not allowed.

## Correspondence
F* st{eqs,flag} models m_eqs (ids) and m_new_solution; fuel models m.inc() polls; solvable models solve_eq returning true. Only the single pushed equation is modelled as visited, since the loop starts at size-1.

## Assumptions
Standard F* library only; no admit/assume. Assumes solve_eq only erases or keeps the equation (manual review). Assumes cancellation is suspended in equality callbacks (per PR comment), so polls succeed there.

## Exclusions
Not audited: seq_axioms.cpp at_axiom bound, fixed_length marking, check_fixed_length/propagate/simplify_and_solve_eqs loops (covered at 88c39c8a), removal of the m_new_solution reset in propagate, re-entrancy of solve_eqs from new_eq_eh (solve_eq may add equalities/propagations), tests (seq_limits.cpp), C++ memory safety and execution. This is a semantic model, not mechanized C++ verification.

## Reproduce
`timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out Z3Pr11331NewEq.fst`
F* 2026.09.27, Z3 4.13.3. sha256 Z3Pr11331NewEq.fst = 4997e4834deb53e9ebbe16f223514c48051400340f628789f97e9ebe9d6b0773