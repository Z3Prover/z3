# F* audit PR #11358 @ fd1663d55c3f33788318c37f372c05d222ff1c82 (base aa71a62f)
Source: fstar/Z3FiniteFieldLemma.fst at head (sha256 8c253b73...eaeb4, 1394 lines). Delta since last audited head af02798e: exhaustive finite-field clause checker (~lines 960-1394).

Partial scope: three changed definitions, three obligation groups. Not full PR coverage.
- within_budget (O1): acceptance implies acc*p^n <= max_assignments (4096), so p^n is never formed unbounded. PROVED.
- for_all_vectors/for_all_heads (O2): success implies f holds on every length-n vector of residues in [0,p). PROVED.
- vector_value (O3): for in-range vectors, every leaf index k(n maps to a residue in [0,p). PROVED.
Counterexample search: no reachable violating witness was found for these obligations; none was claimed.

Correspondence: module Z3PR11358ExhaustiveAudit re-states the PR's definitions verbatim (own module, PR module not imported). Uses only F* stdlib (FStar.List.Tot, FStar.Math.Lemmas). No admit/assume/axioms.
Assumptions: p)=2 and p positive in lemmas (guard `p >= 2` in exhaustive_clause); leaf table has length n.
Excluded (manual review only): eval_ff/eval_bool soundness lemmas (lemma_eval_*, lemma_projections_*, lemma_exhaustive_clause_sound), leaf/leaves uniqueness, find_modulus, closed_ff/D.scoped side conditions, Z3FiniteFieldLemmaTests.fst, C++/OCaml bridge (native.cpp, Z3Native.ml), test tooling, Z3TheoryNormalize/Z3UnifiedProof wiring, and the head module's own full checking. Not mechanized verification of C++ execution or the solver.
Tools: F* 2026.09.27, Z3 4.13.3 (pinned release).
Reproduce: fstar.exe --smt (z3) --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out Z3PR11358ExhaustiveAudit.fst
