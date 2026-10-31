# F* audit of PR #11495 (head 443084f536999ac24c82967e2ba8211692d797c4, base 8fbb275aba0472e862e289c7af1331b3bd5d512c)

Partial-scope audit. Tools: F* 2026.09.27, independent Z3 4.13.3 (pinned release), z3rlimit 10, 120 s timeout, fresh cache.

## Selected changed functions (max 3)
1. `arithmetic_assumptions` / `arithmetic_farkas` (fstar/Z3SortedProof.fst, hunk @@ -951): maps node premises to positive literals and conclusion-clause literals to negative literals, then calls `AR.check_contradiction`.
2. `lemma_arithmetic_assumptions` / `lemma_check_node_cached` Farkas branch (same file).
3. `check_document_epsilon` / `elaborate_epsilon` (same file): appends certified choice equations to assertions.

## Obligations
- O1 (proved, abstract model): assumptions_hold(map pos premises @ map neg lits) == truths(premises) && not any_true(lits). Corresponds to the polarity/clause mapping.
- O2 (proved, abstract model): given a contradiction checker sound for all models satisfying its assumptions, the Farkas node is sound: premises true => some conclusion literal true.
- O3 (proved, abstract model): truths distributes over `@`, so original assertions remain true when elaborated choice equations are appended.
- No counterexample was sought-and-found; no concrete witness was constructed in the time/scope bound (refutation attempt: the mapping is structurally correct, so none was identified by inspection).

## Correspondence and assumptions
F* `t : e -> bool` abstracts `T.truth s bc eq other`; `check` abstracts `AR.check_contradiction`; `sound` abstracts `AR.lemma_check_contradiction` (assumed as hypothesis here - it is proved in the PR's own module, which was NOT re-verified or imported). Integer linearization, Farkas arithmetic (`A.prepare`, `P.accepts`), 4096-occurrence budgets, `integer_formula` guards, Hilbert choice/`E.build`, freshness, cycle checks, and the document-level theorem are NOT mechanized here. The PR's own F* modules were not built (head code must not be executed).

## Exclusions
Z3SortedSkolem.fst (new, 493 lines), Z3SortedArithmetic.fst (new definitions), Z3SortedSkolemTests.fst, OCaml runtime/tool/test changes, build scripts, checker_modules.json, OCAML_CHECKER_REPORT.md, and the Hilbert-epsilon semantic contracts (`hilbert_choice`, `exists_model`) are excluded. Coverage/performance claims in the PR description (including pre-merge measurements, noted performance regressions/timeouts) were not checked. Not an audit of C++ solver behavior, memory safety, or AST plumbing.

## Reproduce
cd fstar-audit && /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out FarkasClauseAudit.fst
Source SHA-256 FarkasClauseAudit.fst: a84615b09e0b3454ffa813319868a6c0dec297271b5b5e46093f71e64f34b600
Marker: fstar-nfv-audit:443084f536999ac24c82967e2ba8211692d797c4
