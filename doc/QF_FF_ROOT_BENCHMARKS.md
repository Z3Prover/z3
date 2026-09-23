# Recognized factors and small roots

The first small-root optimization adds conditional SMT root clauses and a
matching direct quadratic shortcut in the native algebra engine. It does not
implement general modular square roots or a persistent root-set cache.

## Rules and guards

- A product equal to zero implies that at least one factor is zero, because
  prime fields have no zero divisors. Nonzero constant factors are omitted.
- A²=B² implies A=B or A=-B, by factoring A²-B². The square recognizer halves
  even factor multiplicities and recognizes integer-square constant residues.
  This also splits quartics into square equations. No division by two occurs;
  coincident branches in characteristic two, or at zero, are deduplicated.
- For a*X²+c=0 with a nonzero, the algebra engine directly returns ±r when the
  canonical residue -c/a is an integer square r². These are all field roots by
  the same factor identity. An integer nonsquare can still have modular roots:
  all unrecognized cases retain the existing general root algorithm.

Every SMT clause is guarded by the exact original equality atom, even when the
recognizer uses a normalized expression. The emitted clause is not simplified
in a way that replaces that guard. This preserves both assumption dependencies
and the connection to the current SAT assignment. Emission caches are cleared
on backtracking and at a new search. Proof-producing calls remain unsupported;
the necessary certificate obligations are recorded in QF_FF_CERTIFICATES.md.

Products are limited to 16 arguments. Opaque operands, including ordinary wire
definitions, are skipped before normalization to avoid slowing circuit solving.
This can miss opportunities exposed by cancellation; it cannot change answers,
because the original constraints still reach native algebra and exact fallback.

`ff.root_split=false` disables the SMT clause pass, while the algebra engine's
quadratic shortcut remains enabled. `ff root clauses` reports emitted clauses.
To force the previous BV bridge in tests, disable root splitting as well as
setting `ff.max_steps=0`.

## Validation

Release and Debug pass:

- 240 mixed formulas independently checked by exhaustive small-field enumeration;
- 904 pure-algebra quadratic and exhaustive root-exclusion checks;
- zero/negative roots, characteristic two, modular-only squares, products of
  sums, false equality guards, tracked cores, assumptions, push/pop and reset;
- the existing small/large combination suites, including 105 exhaustive UF
  cases per solver path, finite cardinality, arrays, datatypes, model evaluation,
  forced BV fallback and cancellation recovery;
- five C++ tests covering finite fields, SMT context, model evaluation and
  parametric datatypes.

The pure-field CLI/API regression also passes 500 formulas against enumeration
and cvc5, with 665 successful standalone native tactic checks.

## Measurements

Results are in [root-clauses.json](../tests/finite_field/results/root-clauses.json).
The benchmark compares the saved pre-optimization binary and the new binary,
records their hashes, and checks original SAT assertions separately from timing.
The generated workload and public Poseidon parameter fixtures are in the test
directory. This is not an exported production Blaster workload.

Fresh-process medians include parsing and field validation. Separate solver-only
measurements exclude setup. Disabling root splitting in the new binary does not
reproduce the old engine, because the quadratic shortcut is still present.

All 16 generated cases pass in both Z3 paths, before and after, in all three repetitions. For each SAT case, a separate current-Z3 run checked its model against every original assertion.

BN254 fresh-process medians, in milliseconds:

| Case | Before SMT | After SMT | After default | cvc5 default | cvc5 split |
| --- | ---: | ---: | ---: | ---: | ---: |
| Quadratic UF contradiction | 42.11 | 25.21 | 24.91 | 32.49 | 27.26 |
| Quadratic UF SAT model | 30.04 | 24.64 | 25.30 | 38.14 | 24.21 |
| Array index contradiction | 44.56 | 24.64 | 24.83 | 52.25 | 84.45 |
| Quartic UF contradiction | 86.68 | 24.79 | 24.88 | 43.95 | 29.34 |

Solver-only BN254 medians are 0.136 ms for the mixed quadratic, 0.171 ms for the mixed quartic, and 0.026 ms for the standalone algebra quadratic. These exclude field creation and other setup, so they must not be compared directly with process timings.

Across the eight Poseidon SAT/equivalence sentinels over both fields, before/after medians remain within 1.1% in both Z3 paths. The initial broader recognition scan incurred a small direct-SMT overhead; skipping opaque wire operands removed it. These short local measurements support no material regression on this suite, not a statistical guarantee for other circuits.

The small mixed cases now match or improve on several cvc5 split results, although that backend remains slightly faster on some SAT root cases. General modular square-root extraction and root-set reuse remain future work.

```sh
PYTHONPATH=build-ff-cmake/python Z3_LIBRARY_PATH=build-ff-cmake \
  python3 tests/finite_field/test_ff_root_clauses.py
PYTHONPATH=build-ff-cmake/python Z3_LIBRARY_PATH=build-ff-cmake \
  python3 tests/finite_field/benchmark_ff_roots.py \
    --baseline /path/to/saved/pre-optimization/z3 \
    --cvc5 /path/to/field-enabled/cvc5 --repeat 3
```
