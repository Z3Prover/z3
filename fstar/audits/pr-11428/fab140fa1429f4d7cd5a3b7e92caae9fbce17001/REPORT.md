# F* audit PR #11428 @ fab140fa1429f4d7cd5a3b7e92caae9fbce17001 (base bfb47e299d84)
Partial scope: `lp_relaxation::minimize_cost` (src/opt/opt_lp_relaxation.cpp L466-575, sha256 fec962bf...a0eb), `maxcore::bounds_meet`/`get_lower`, lower-bound rounding. Three obligations, abstract integer model (weights scaled by lattice_step denominators).

| Obligation | Result |
|---|---|
| O1: cost >= literal_weight - relaxed max (C++ `bound = literal_weight - value`), assuming integral assignments are feasible for the relaxation and the maximum is certified by the unsat strict cut | proved |
| O2: `step*ceil(bound/step)` stays <= every cost that is a multiple of step and >= bound; clamp at 0 sound | proved |
| O3: `bounds_meet`: lower>=upper with a model of cost=upper implies optimality | proved |

No counterexample was constructed.
Assumptions (manual, not mechanized): relaxation of each hard constraint is a sound over-approximation (relax_literal/add_hard/dropped constraints); the LP maximum is exact when `certified`; weights nonnegative; inf_eps handled by C++ check (finite, non-infinitesimal).
Exclusions: add_hard/relax_literal/relax_indicators and relaxation encoding, rounding-to-assumption logic in relaxation_bounds, hill-climb loop edits, m_relaxation_closed/commit_assignment change, check_sat side effects, params, tests, cancellation/rlimit handling, memory safety. This is not verification of C++ execution.
Base dependencies: none beyond F* standard library.
Versions: F* 2026.09.27; Z3 4.13.3.
Reproduce: `/tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out Z3MaxsmtLpRelax.fst`