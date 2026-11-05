# F* audit of PR #11211 at 02eb8bbc2971d13416287f6dda30d55d7078c305 (base c1c2e52d1386e9969c80a3d5df7e15cd4a6ef626)

PR open at this SHA; the only existing marker was for ef62c14a (a different head), so this revision is new. Prior audit covered monotonicity, bounding (last case), prime; this run covers different functions.

Source: src/ast/rewriter/arith_swine.cpp @ head (448 lines; sha256 of decoded content 7f2b84a004eeb409bf6b7675a3e3994c132df734fba6f107f5ccdd1949885141), arith_swine.h sha256 19de765976d70c323316cfd5d3d67866dc03c04dfe2f3e606821b7aa3ff5fc51. Fetched via the contents API, saved under /tmp/gh-aw/agent/src/.

## Scope (partial: 2 functions, 4 checked lemmas (3 obligations; symmetry has e>=0 and all-e variants))
1. arith_swine::symmetry, x<0,y>=0 branch (L91-112): guard b<0; lemma b^e = (e mod 2 = 1 ? -((-b)^e) : (-b)^e). PROVED (symmetry_valid).
2. arith_swine::induction (L232-273): guards base_p = base_q, e>=0, e_q - e_p = d (d>0) => b^(e+d) = b^e * rhs, where rhs is the d-fold product (d<=64, symbolic base) -- PROVED (induction_valid) -- or numeral x^d (numeral base / specialized base=x) -- PROVED (induction_numeral_valid).
Refutation: no witness sought was found; the obligations are valid so none exists for the modeled lemma shapes. A separate unmechanized brute-force check (Python, x0,y0<=8, x,y<40) found no violation of the lower-bound secant in interpolation(); not a proof, not published.

## Correspondence and assumptions
- F* pow b e (e:nat) models a.mk_power for non-negative exponent; unbounded mathematical ints. mod 2 in F* (% on int) is used as Z3 mod with positive divisor; for exponent e>=0 it equals e mod 2 in {0,1}.
- The proofs establish semantic validity of the emitted implications, given the guards. They do not mechanize C++ execution, AST construction (mk_ite/mk_implies plumbing), rewriting via m_rw, memory safety, or the value() callback.
- Symmetry: the C++ guard is only base<0 (no exponent guard). symmetry_valid_any proves it for all integer e using zpow, which mirrors compute_power (e<0: 1 if b=1, +-1 by parity if b=-1, else 0). That zpow matches Z3's semantics for negative exponents is an assumption taken from compute_power, not independently verified.
- Induction: the d-fold product branch needs d<=64 (checked in C++); the proof holds for all d>0.
- Inherited: F* core/standard library, Z3 4.13.3 backend, F* 2026.09.27.

## Exclusions
check_model, compute_power, bounding (all cases), monotonicity, prime, interpolation, interpolant, add_assumptions, should_research, check; the induction guard when p.exponent<0 is excluded by the emitted e>=0 guard; arith_rewriter.cpp, arith_decl_plugin, theory_lra.cpp, arith_solver.cpp, sat_solver.cpp, tests, API header, purify_arith_tactic, PR's own fstar/*.fst and ZWINE_NFV_REPORT.md (not imported/trusted), vercors artifacts, all other PR files. Not full PR coverage.

## Reproduce
cd /tmp/gh-aw/agent/fstar-audit && bash run.sh   (fstar.exe --smt .../z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out SwineAudit2.fst, 120 s timeout)
