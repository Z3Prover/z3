# Original-input Alethe/PAC pipeline: second v2 milestone

The opt-in pipeline now exports the finite-field Alethe/PAC format used by the
FMCAD 2026 work and runs real external checkers. It uses the public companion
Carcara finite-field branch and FFPacheck, with pinned sources and a small local
FFPacheck completion patch. It does not claim that the artifact VM contains
these exact revisions, stock Carcara compatibility, or Lean acceptance.

The [third milestone](QF_FF_BOOLEAN_PROOFS.md) now adds checked Boolean/ITE
reasoning and deep-input support. The results and narrower profile documented
below describe the second milestone; the CLI automatically selects the new
profile for inputs outside the legacy literal-conjunction path.

## Run and independently recheck

Build the external checkers using
[`proof_checkers/README.md`](https://github.com/RSoulatIOHK/z3test/blob/df7d7c5f66f603fc07991ece60c9a3e70eb91828/regressions/finite_field/proof_checkers/README.md).
Set `CARCARA` and `FFPACHECK` to their absolute executable paths:

```sh
python3 scripts/ff_proof_pipeline.py problem.smt2 --out /tmp/ff-proof \
  --z3 build-ff-cmake/z3 --carcara "$CARCARA" --ffpacheck "$FFPACHECK"
python3 scripts/ff_proof_pipeline.py --check --out /tmp/ff-proof \
  --carcara "$CARCARA" --ffpacheck "$FFPACHECK"
```

Production requires a new output directory. Rechecking consumes the stored
original input, DAG, polynomial input, Alethe and PAC files; it does not overwrite
or silently regenerate the proof under test. A JSON receipt records binary/file
hashes, exact commands, stage timings and logs. A receipt is historical evidence,
not a substitute for rechecking files after they change. Nonzero exit means the
pipeline has not certified the problem. Unsupported input and bounded
reconstruction failure are never reported as SAT.

The legacy `z3-ff-alethe-pac-v1` original-input profile is a conjunction of field equalities and
**disequalities**, over one prime field, with constants, nullary definitions,
lets, named assertions and addition/multiplication/negation. The polynomial
reconstruction remains the existing bounded scalar `ff-certify` command. There
are no changes to default solving, native Z3 proofs, or the optimized solver's
execution path. This is standalone reconstruction, not proof logging for every
successful Z3 UNSAT answer.

In this legacy profile, general Boolean formulas, Boolean declarations, ITEs, UF/theory-combination
steps, implicit field/root reasoning, incremental scripts, mixed fields and
`ff.bitsum` are outside this external-checker profile. The legacy independent
positive-equation checker continues to support bitsum. The existing 200-level
S-expression limit and other bounded checker/reconstructor limits remain.
The CLI limits each external stage to ten seconds and each output stream/file to
32 MiB; the benchmark additionally enforces a single ten-second deadline for
the entire per-input pipeline. There is no total-process memory cap in this new
screen, and the measured elapsed times include subprocess supervision.

## Proof chain and trust boundary

1. Parse the original formula independently. Project conjunctions with Alethe
   `and` steps, retaining the original assertions as `assume` commands.
2. Replace `l != r` by `(l-r)*w - 1 = 0` with a fresh field witness. This is
   equisatisfiable because a nonzero field element has an inverse. The Alethe
   witness is the artifact's explicit `choice` term, with a fresh bound name;
   Carcara's `ff_diseq` checks it. `equiv1` and `resolution` transfer the premise.
3. Reconstruct and independently replay the polynomial DAG against those exact
   equations. `poly_simp`/`poly_simp_rel` justify polynomial normalization in
   Carcara. These are the names accepted by the pinned public checker; the
   paper uses `ff_poly_norm`/`ff_poly_norm_eq` terminology.
4. Emit shared PAC axioms and linear combinations, pruning DAG nodes that are
   not ancestors of the contradiction. Preserve the checked input ordering and
   a fixed variable map. Multiplication and addition nodes become PAC `l`
   steps, ending in a derivation of `1` and `unsat`.
5. Use `and_intro` and `ff_poly_conversion` to form the corresponding ideal;
   embed the PAC stream in the artifact's `ff_pac` rule. Check the PAC separately
   with FFPacheck, then check Alethe with Carcara invoking FFPacheck again.

The independent check and the exact-byte binding are mandatory, because the
inspected Carcara bridge checks the PAC payload without binding its axioms,
modulus or variable map to the Alethe premise. A regression reproduces raw
Carcara acceptance of an unrelated PAC contradiction against a satisfiable SMT
input, and verifies rejection by our pipeline. Thus **Carcara acceptance alone
is insufficient**. The Python parser, witness bridge, arithmetic checker and
canonical exporter form part of the trusted checking boundary. Z3 and its
Groebner search are not trusted by that check.

FFPacheck's public revision also returned success at incomplete EOF and failed
to close a top-level derivation of 1. The recorded patch fixes these two cases
and adds a missing C++ include. It does not fix or claim to audit all of the
checker's general root/branch rules; this pipeline emits no such rules.
Exact original-input checking also protects against accepting trailing or
substituted proof material. See the checker README for source locations,
checksums, reproducible builds and the five axiom-only upstream fixtures that
are now intentionally rejected. No upstream issue has been submitted.

## Validation

```sh
python3 z3test/regressions/finite_field/test_ff_proof_pipeline.py --z3 build-ff-cmake/z3 \
  --carcara "$CARCARA" --ffpacheck "$FFPACHECK"
python3 tests/finite_field/benchmark_ff_proof_pipeline.py \
  --manifest tests/finite_field/results/paper-artifacts/manifest.json \
  --corpus tests/finite_field/results/paper-artifacts/corpus.zip \
  --out /tmp/ff-proof-screen --z3 build-ff-cmake/z3 \
  --carcara "$CARCARA" --ffpacheck "$FFPACHECK" --timeout 10 --jobs 4
```

On 2026-09-24, the end-to-end regression suite accepted 29 proofs through both
external checkers, spanning primes 2, 3, 7, 4294967311 and a 254-bit prime. It
covered nonlinear equations, disequalities, nested conjunctions, lets, nullary
definitions, quoted identifiers, witness/binder collisions, negative numerals
and named assertions. Twenty-five corruption, scope, SAT, incomplete-proof and
deadline checks passed. The legacy independent certificate suite also passed.
The patched FFPacheck upstream suite had 498/503 successes: the remaining five
files contain only a modulus and axioms, without proof completion. All 22
explicit negative fixtures were rejected.

The same fixed artifact subset as the previous screen contains 408 member paths
and 390 distinct inputs. The new ten-second **whole-pipeline** screen produced:

| Outcome | Previous certificate screen | This pipeline |
|---|---:|---:|
| Original-input certificates checked | 0 | **135** |
| Unsupported profile | 390 | **255** |
| In-profile reconstruction/check failure or timeout | 0 | **0** |

The 135 accepted inputs are compilation-determinism instances: 47 `zokref`, 46
`zokcirc`, and 42 other compilation backends. The 255 unsupported inputs report
185 Boolean-sort restrictions and 70 nesting limits (first-error categories;
some deep inputs also contain Booleans). Every accepted proof passed our
independent check, FFPacheck, and Carcara with FFPacheck.

For those 135 inputs, median total elapsed time was **0.128 s**, maximum
**1.043 s**. Median DAG/PAC/Alethe sizes were 7,447 / 18,002 / 110,373 bytes;
maxima were 252,654 / 2,307,776 / 2,577,169 bytes. Four concurrent workers were
used, so these timings are throughput-screen measurements, not isolated solver
microbenchmarks. Unmodified normal Z3 previously solved 382/390 in its separate
screen. That is solver coverage, not proof coverage. No new CVC5 production,
CPC/Lean reconstruction, or competitive performance comparison was run here.

Full inputs, proofs, receipts, selection, binary hashes and timings are archived
under `tests/finite_field/results/fmcad-proof-pipeline-v2/` (ignored benchmark
artifacts). A small checked disequality fixture is tracked under
`z3test/regressions/finite_field/fixtures/certificates/artifact-disequality/`.

## Priorities identified at this milestone (see the third-milestone update)

- Replace recursive/limited front-end expansion with a bounded shared term
  representation, to support deeply nested artifact inputs without duplicating
  let-bound terms throughout the Alethe output.
- Produce checked Boolean/ITE preprocessing and case reasoning. Do not discard
  Boolean structure or certify a solver-selected conjunction as the full input.
- Extend DAG evidence to field/root contradictions and theory-combination
  lemmas; PAC already provides a target language for root/branch evidence.
- Close the upstream PAC-to-Alethe binding gap, then evaluate CPC/Lean-SMT as a
  separate consumer. Neither task is complete in this milestone.
