# F* audit of PR 11474 @ 66ccdcaa3bd663aaa6fee2367ff86a406e8f7c09 (base d687b6a18d03834ec2bfaa72647890c444748a09)

Scope (partial): one changed function, `sat::solver::resolve_conflict_for_unsat_core`, the m_core level-0 filter (sat_solver.cpp ~2828-2837 at head). Head blob 297c28d9da3d71a3e41c60faf365f9f076010de2 (sha256 903a5c20263b65c85dfc2b83e87078dc0f36e89eb0cd6f2a977978c2d5586154); base file sha256 8a78407a5cfb4d9f0eb0896e2a052d236c465f2c2ad1dbf8f5b1cf6ad4819644.

Change: `if (lvl(m_core[i]) > 0)` became `if (lvl(lit) > 0 || value(lit) == l_false)`.

## Obligations (all proved, F* model SatCoreLevel0.fst)
- O1 proved: each literal dropped by the new filter has lvl 0 and is not false, i.e. it is true at level 0 and implied by the clauses (soundness of dropping).
- O2 proved: every level-0-false literal in the core is retained.
- O3 proved: the new filter keeps everything the old one kept (the core only grows, so no previously sound core loses literals).
- Refutation of the old behavior: concrete witness showing the old filter drops a level-0-false assumption (`old_cex`); this is a bug in the base, fixed by the PR, not a counterexample against the PR.

## Mapping and assumptions
Entry = (lvl(lit), value(lit)==l_false). Assumed: core literals are assigned (not l_undef); a level-0 assigned literal that is not false is true and entailed by the clause set (inherited solver invariant, not proved here); O1's `entailed` is a restatement of this assumption, so O1 is largely definitional. Not modelled: how core literals are collected (process_antecedent_for_unsat_core), the early return when m_conflict_lvl==0 and !m_drat, m_core_minimize/m_mus afterwards, whether the resulting core is still unsat-sufficient in all paths (e.g. size<=1 cores skip the filter), and the tests. The semantic model is not a mechanized proof of the C++, memory safety, or the whole solver. Note value(lit) semantic: lit is the assumption literal itself, so l_false means the assumption is contradicted by the level-0 trail.

## Exclusions
src/test/CMakeLists.txt, src/test/main.cpp, src/test/sat_unsat_core.cpp (test plumbing/new test) not audited.

## Reproduce
timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out --include /home/runner/work/z3/z3/fstar SatCoreLevel0.fst
