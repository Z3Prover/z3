# V2 milestone 1: independently checked polynomial refutations

The new `ff-certify` shell command reconstructs a bounded polynomial
contradiction directly from the current assertions. The output is a shared
arithmetic derivation DAG, with a separate exporter and checker for an
experimental Alethe finite-field extension. Both checkers normalize the original
problem independently and verify a derivation of 1 = 0 using modular integer
arithmetic. Neither checker calls Z3 or runs Groebner search.

This establishes the first large-prime end-to-end certificate path. It does not
certify the optimized solver's entire execution or change its defaults. It is a
separate scalar reconstruction pass, so its solving coverage and timing need
not match the production solver. Standard `get-proof` calls remain unsupported
for FF, as do certificates for root branching, disequalities and combinations
with other theories. A checked FF conflict is not a complete mixed-theory proof.

The [format and rule contract](QF_FF_CERTIFICATES.md) gives exact scope,
resource limits, extension status and reproduction commands. A checked large
prime example is tracked in
[`fixtures/certificates`](../tests/finite_field/fixtures/certificates/large-prime.smt2),
alongside its DAG and Alethe-extension outputs. No compatibility with unmodified
Carcara or other Alethe consumers is claimed.

## Validation

All **21 regression commands** pass: the existing 20-command FF suite plus the
new certificate suite. Existing field arithmetic, model construction, cores,
root reasoning, theory combination and native proof-request rejection remain
covered. No fresh cvc5 comparison is part of this milestone.

The new suite checks **83 pairs** of DAG and Alethe-extension certificates,
including characteristics 2/3/7, primes on either side of the 32-bit boundary,
and the 254-bit prime used in the example. Fixtures cover nonlinear polynomial
contradictions, S-pairs, constants, signed coefficients, bitsums, conjunctions,
quoted variables, nullary definitions and simultaneous lets.

Of 144 independently enumerated random systems over F2/F3/F5, all 44 UNSAT
systems yield accepted certificates and all 100 SAT systems yield no
certificate. These tests explicitly assert the field equations x^p-x=0 and
y^p-y=0; they do not claim an implicit field-axiom proof rule has been added.

The suite rejects **28** corrupted, truncated or wrong-problem certificates:
modified coefficients, input normalization, missing/forward references,
changed fields and variables, false roots, invalid conclusions and proof holes.
Resource tests force exhaustion of work, terms and nodes. C++ tests additionally
check output atomicity, unchanged inputs, cancellation and subsequent reuse.
A final shell lifecycle check produces a certificate inside a pushed context,
pops it and recovers the original SAT result; its isolated certificate is also
checked against the exact active assumptions.

The extension-field-only root example x^2+1=0 over F3 yields
`no-polynomial-refutation`, as intended: that finite-field contradiction cannot
be justified by the supplied polynomial ideal alone. Unsupported mixed fields,
UF terms, disequalities and Boolean alternatives are explicitly refused.

## Bounded cost screen

Eight generated instances assert x^d=0 and x*y=1, for d in {4,8,16,32}, over F7
and the example's 254-bit prime. Five isolated repetitions alternate the order
of the frozen round-12 binary and the new binary with certificates disabled,
then invoke standalone certificate production. All regular checks return UNSAT;
all **40 generated certificate pairs** pass both independent checks.

These are small certificate-cost fixtures, not real-circuit benchmarks or a
corpus coverage study. Process timings include launch, SMT-LIB parsing, field
sort construction and command output. Peak RSS is the producer process's
maximum resident set, measured by macOS `/usr/bin/time -l`; it excludes the
Python checker. Checker timings run inside Python and exclude interpreter
launch. Export time is not included in either checker timing.

| Field | Degree | Producer median (ms) | DAG nodes | DAG bytes | Alethe bytes | DAG check (ms) | Alethe check (ms) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| F7 | 4 | 8.770 | 18 | 402 | 2,781 | 0.432 | 1.014 |
| F7 | 8 | 8.618 | 34 | 706 | 5,369 | 0.586 | 1.791 |
| F7 | 16 | 9.223 | 66 | 1,410 | 11,121 | 1.145 | 4.852 |
| F7 | 32 | 8.846 | 130 | 3,232 | 24,989 | 2.112 | 12.091 |
| 254-bit | 4 | 28.458 | 18 | 1,162 | 7,189 | 0.509 | 1.221 |
| 254-bit | 8 | 31.767 | 34 | 2,074 | 14,033 | 0.698 | 2.969 |
| 254-bit | 16 | 30.726 | 66 | 3,994 | 28,297 | 1.115 | 5.264 |
| 254-bit | 32 | 29.768 | 130 | 8,248 | 59,189 | 2.268 | 12.972 |

Producer peak RSS ranges from 29.53 to 29.91 MiB across these cases. The Alethe
extension prints each conclusion explicitly and repeats sort annotations;
its larger size/checking cost is visible even on this small screen. The internal
DAG avoids expansion of the full polynomial multipliers against original inputs.

Summed per-case median solve time with certificate production disabled is
161.444 ms for the frozen baseline and 162.376 ms for the new build: **+0.58%**.
The short, launch-dominated cases do not establish broad performance equivalence,
but show no systematic large penalty on this screen. More importantly, normal
solving allocates no proof recorder or per-polynomial proof metadata. No default
algorithm or parameter has changed, and no new performance win is claimed.

## Reproduce and inspect

```sh
cmake --build build-ff-cmake --target z3 test-z3 libz3 -j8
build-ff-cmake/test-z3 finite_field
python3 tests/finite_field/test_ff_certificates.py --z3 build-ff-cmake/z3
python3 tests/finite_field/benchmark_ff_certificates.py \
  --z3 build-ff-cmake/z3 \
  --baseline tests/finite_field/results/performance-round12/binaries/expanded \
  --out /tmp/ff-certificate-cost --repeat 5
```

Local evidence is archived under
`tests/finite_field/results/certificates-v2-slice1`: regression outputs,
benchmark inputs, both encodings, all individual timing/RSS samples, binary
hashes and environment metadata. That results directory is intentionally ignored
by git; the generators, tests, example and this summary are tracked.

The next v2 steps are proof-producing preprocessing and native theory-lemma
attachment with exact premises, followed by inverse witnesses, finite-field
root certificates and Boolean/theory-combination composition. Alethe
interoperability requires agreement on rules and support in the target checker.

## Real-artifact follow-up

The first full artifact screen is in [QF_FF_FMCAD_PROOF_BENCHMARK.md](QF_FF_FMCAD_PROOF_BENCHMARK.md):
382/390 ordinary UNSAT answers at ten seconds, but 0/390 certificates because
all original queries exceed the first milestone's positive-equality input scope.
The synthetic certificate-cost fixtures above must not be read as artifact
certificate coverage.
