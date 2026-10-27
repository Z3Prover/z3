# F* audit of PR #11358 @ 8b728dcc55e3533f46cb77401ac141ca4087e732 (base aa71a62f)

**Verdict: inconclusive (publication limit), not a finding against the PR.**
The tool payload limit (10 KiB) prevents bundling the 33 KB audited module, so no proof module is published and per policy obligations are reported inconclusive.

## Scope (partial)
Head `fstar/Z3FiniteFieldLemma.fst` (contents API at head SHA; sha256 51cd07d6244a1ebf3295b1fbb1ab63b003d414e477a91e40dc3f7a8556054f19, 840 lines). Selected: `term_equivalent`, `eq_truth_equivalent`, `eq_eq_equivalent` with their lemmas (to_poly/combine soundness, zero-poly => equal, zero/nonzero-constant difference => eq true/false, unit-scaled zero sets).

## Check performed
Unmodified head module checked by F* 2026.09.27 with Z3 4.13.3 (pinned backend), base modules from the trusted checkout (aa71a62f), fresh cache, CLI `--z3rlimit 10` (module's own `#set-options --z3rlimit 40` overrides), exit 0, "All verification conditions discharged successfully", 15s. No admit/assume/axiom (grep hits only comments). No counterexample witness was found or sought beyond reading guards.

## Assumptions
`ff_model i project` is a hypothesis (residues mod p; numeral denotes n; ff.add/mul/neg/bitsum are mod-p ops; equal values iff equal residues for closed terms); not mechanized against Z3's C++ FF plugin. Inherited: Z3AstTheory, Z3ValueTheory, Z3ResolutionProofTheory, Z3Definitions, Z3BooleanRewrite, F* stdlib. p need not be prime.

## Not mechanized / excluded
C++/OCaml bridge (`native.cpp`, `Z3Native.ml`), marshalling of FfNum params, `Z3NativeProof.fst`, `Z3TheoryNormalize.fst` (dispatch skimmed only), tests, docs, tools, helper search functions (egcd/inverse_mod/collect; untrusted), memory safety, whole solver.

## Reproduce
fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include (base)/fstar --cache_dir cache --odir out --z3rlimit 10 Z3FiniteFieldLemma.fst
