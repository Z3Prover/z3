# F* audit of PR #11211 at e10c5f6f35a37fd427e47b7c15acd2c4dbdb4aea (base c1c2e52d1386e9969c80a3d5df7e15cd4a6ef626)

New head vs earlier audited heads (02eb8bbc, ef62c14a, 317d28d0, ced49cb4); this head changes only src/tactic/arith/purify_arith_tactic.cpp. Source: purify_arith_tactic.cpp @ head, process_power lines 436-486, snapshot sha256 d5f5d30df8d0e6c5a963c66140ca4b6ad7785f07955386f2c7bd86ce5d8fbcbe (decoded; saved under /tmp/gh-aw/agent/src). Tools: F* 2026.09.27, Z3 4.13.3 (pinned release backend).

## Obligations (all PROVED in SwineAudit5.fst)
- O1 guard: after y=0 and non-numeral exits, accept iff y non-integer and numerator is one, hence y=1/n with n>=2 (lemmas o1, o1_rejects). Other exponents return BR_FAILED before any fresh variable or cache entry is created.
- O2 even n: constraints (x<0 \/ (x=k^n /\ k>=0)) and (x>=0 \/ k=negroot) have no conflicting branches and determine k uniquely (even_ok, using injectivity of n-th power on naturals, mono/inj_nonneg).
- O3 odd n: x=k^n has at most one integer solution, so the fresh k is uniquely defined (odd_unique, pow_neg).

No counterexample sought-and-found; obligations were valid so none exists for the modeled shapes.

## Correspondence and assumptions
F* pow models mk_power with natural exponent n=denominator(y); k,x modeled as mathematical integers (ordered ring) rather than reals; uniqueness over integers is an under-approximation of the real-valued claim (real k uniqueness is not proved). neg-root is an opaque value nr (its semantics not modeled). Even-n case x<0 only checks consistency, not that neg-root is correct. Not mechanized: C++ execution, AST construction/allocation order, memory safety, cache/proof plumbing (push_cnstr_pr, mk_def_proof), already_processed. SASSERT(!is_int(x)) is debug-only. Inherited: F* core/standard library (FStar.Math.Lemmas), Z3 4.13.3. No admit/assume.

## Exclusions
All other PR files: arith_swine.cpp (covered in prior audits for some functions), arith_rewriter.cpp, arith_decl_plugin, theory_lra, arith_solver, sat_solver, algebraic_numbers, cmd_context, tests, API, PR own fstar/*.fst and ZWINE_NFV_REPORT.md, vercors artifacts. Other functions of purify_arith_tactic.cpp not audited.

## Reproduce
cd /tmp/gh-aw/agent/fstar-audit && /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out SwineAudit5.fst  (120 s timeout; fresh cache; no --include needed, no base modules imported)