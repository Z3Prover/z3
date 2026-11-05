# F* audit of PR #11211 at ef62c14a164d04569b07a5910c2627ce47a9114b (base c63bc780290944fb7a20660747bc5de543b8f1bf)

Source audited: src/ast/rewriter/arith_swine.cpp @ head (448 lines, sha256 7f2b84a0...5141 of decoded content), lines 116-139, 141-190, 192-230.

## Scope (partial: 3 functions, 1 obligation each)
1. arith_swine::monotonicity (L116-139): lemma guards base_p>1, exp_p>0, base_q>=base_p, exp_q>=exp_p, one strict => q^ > p^. PROVED (monotonicity_valid).
2. arith_swine::bounding, last case (L175-185): b>1, e>1, b+e>4 => b^e > b*e+1. PROVED (bounding_valid).
3. arith_swine::prime (L192-230): for d prime, (d | b^e) <=> (d | b /\ e != 0) for e>=0. PROVED (prime_valid) assuming d satisfies Euclid's property (`euclid d`, a hypothesis, not an axiom).

No counterexample was sought-and-found; refutation attempts were not needed because all obligations were proved.

## Correspondence and assumptions
- F* `pow b e` models Z3 integer power for non-negative exponent (a.mk_power with e>=0 semantics). Integers are unbounded mathematical ints.
- Lemma conclusions in C++ use a.mk_gt over terms equal to pow; the proof covers the semantic validity of each emitted implication, not C++ execution, rewriter plumbing, memory safety, or the model-value extraction.
- prime: the C++ witness d is (a) a trial divisor with smaller primes divided out of both x and v, or (b) a remaining cofactor with divisor^2 > it, hence prime. That d is prime was reviewed manually, NOT mechanized (only the Euclid property is assumed in F*). The case x==v exit and the p.y<=0 / x<2 skips were not modeled; the lemma is emitted under exponent>=0 guard, matching the proof (e=0 gives 1, not divisible by d>=2).
- Inherited: F* standard library (FStar.Math.Lemmas), Z3 4.13.3 backend. F* 2026.09.27.

## Exclusions
All other changes: compute_power, check_model, symmetry, bounding other cases, arith_rewriter.cpp, arith_decl_plugin, theory_lra.cpp, arith_solver.cpp, sat_solver.cpp, tests, API header, purify_arith_tactic, the PR's own fstar/*.fst modules and ZWINE_NFV_REPORT.md (not imported or trusted), vercors artifacts.

## Reproduce
cd /tmp/gh-aw/agent/fstar-audit && /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out SwineAudit.fst
