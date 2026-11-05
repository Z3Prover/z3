# F* audit of PR #11367 at d3bfe793b86e90592844bceba7ba46bc4aa2fa9f (base 48a710a9c45882fd730a16477c8e2a1084acc77b)

Scope (partial): 3 changed functions, selected from fstar/Z3BvWord.fst, Z3BvFresh.fst, Z3ProofDocument.fst.
1. Z3BvWord.projection / lemma_projection(_bits): `bvule 1 (extract b b src)` reads bit b. 
2. Z3BvFresh.bit_definitions: symbol k defined as projection of bit start+k.
3. Z3ProofDocument.document_definitions: not audited (inconclusive; see exclusions).

Obligations
- O1 proved: projection n b == (bit b of n <> 0).
- O2 proved: for n < 2^(start+count), bits_number of projection bits == n / 2^start (the key step of lemma_projection_bits / reflect).
- O3 proved: bit_definitions maps symbol k to bit start+k, one definition per symbol.
- O4 inconclusive: document_definitions fall-back/budget logic, freshness and acyclicity. Not modelled.

Correspondence: AuditProjection models extract as (n / 2^b) % 2, matching Z3BvTheory.bv_extract (hi=lo=b) and unsigned ule on width 1. It is an arithmetic abstraction, not the PR's expr/eval modules; PR's own lemma proofs were not re-run or trusted. No counterexample was found or attempted beyond this reasoning.

Assumptions: standard FStar.Math.Lemmas only; no admit/assume. F* 2026.09.27, Z3 4.13.3 (pinned).

Exclusions: Z3ProofDocument.document_definitions, add_definitions, reconstruction_equations, expression_budget fallback, equivalent/projection_equivalent, lemma_projection width=1 special case, test_native_bridge.ml, OCAML_CHECKER_REPORT.md, all C++ execution/memory safety.

Reproduce (in fstar-audit dir, fresh cache/out):
fstar.exe --smt .../z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out AuditProjection.fst (and AuditDefs.fst); both exit 0.
