# F* audit of PR #11358 @ af02798ee834bc24fde042f0fdab38d35edfd179 (base aa71a62f)

**Verdict: proved for the three selected obligations (partial scope).** No counterexample was sought-and-found; none established.

## Scope (3 functions, 3 obligations each max)
Source: `fstar/Z3FiniteFieldLemma.fst` at head (944 lines, sha256 e778d10507f3115340b077fe82baa68cf337935b55429ee01294dfe4a23b277d, fetched via contents API).
1. `bitsum_mod` (l.79-82): equals exact sum x_i*2^i reduced mod p (`lemma_bitsum`). Matches C++ `ff.bitsum` positional semantics (ff_decl_plugin.cpp: not associative/commutative).
2. `calculate` negation branch `(0-x) % p` (l.84-88): canonical residue and additive inverse (`lemma_neg`).
3. `same_zero_set` / `scale_witness` unit-multiple branch (l.752-769): d1=k*d2, d2=w*d1 mod p implies equal zero sets (`lemma_scaled_zero`, `lemma_same_zero`), for any p>=1 (prime not needed).

## Verification
- Head module `Z3FiniteFieldLemma.fst` was checked unmodified against trusted base modules: exit 0, all VCs discharged (~15s, fresh cache). This does NOT make it published; it is too large for the payload.
- Generated module `Z3PR11358FfAudit.fst` is self-contained (stdlib only, no admit/assume/axioms), re-states the integer-level definitions and proves the laws; fresh cache, exit 0.
- F* 2026.09.27, Z3 4.13.3 (pinned release backend, not PR-built).

## Assumptions
The PR's `ff_model` (residues mod p, numeral denotes n, add/mul/neg/bitsum are mod-p ops, equal values iff equal residues on closed terms) is a hypothesis, not mechanized against Z3's C++ FF plugin. Inherited: Z3AstTheory, Z3ValueTheory, Z3ResolutionProofTheory, Z3Definitions, Z3BooleanRewrite, F* stdlib. The audit module restates definitions by hand; correspondence to the PR text is manual.

## Excluded / not reviewed
C++/OCaml bridge (native.cpp, Z3Native.ml: modulus via get_finite_field_sort_size, FfNum numerals), Z3NativeProof.fst marshalling, Z3TheoryNormalize.fst dispatch (only skimmed: adds FF.equivalent and ff_model existential to normalization_model; a stronger model hypothesis is only sound if ff_model is satisfiable for relevant models), Z3FiniteFieldLemmaTests.fst, to_poly/pprod/eq_eq/term_equivalent/ite_eq_equivalent proofs (only covered by the head-module check), docs, tools, memory safety, whole solver.

## Reproduce
```
F=/tmp/gh-aw/fstar/bin/fstar.exe
$F --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --cache_dir cache --odir out --z3rlimit 10 Z3PR11358FfAudit.fst
```
