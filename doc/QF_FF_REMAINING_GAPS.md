# The 19 remaining cvc5-only cases after round 6

This diagnoses the 19 cases in the round-6 exact-hash comparison where historical
cvc5 1.3.4 GB or split returned a definite answer within 10 seconds and the new Z3
default timed out. It does not replace the primary benchmark measurements.

Fresh diagnostic runs use the frozen round-6 binary, a 2-second internal timeout,
a 4-second external timeout and four workers. Each case is also run through an
explicit algebra-only portfolio with a 20-million-step allowance. No solver
source or defaults were changed for this investigation.

## Observed failure modes

The default route records **9 algebra-work budget exhaustions**, **7 matrix-limit
exhaustions**, and **3 polynomial-size exhaustions**. All 19 enter the native
bit-vector fallback. Those are early failure points; the primary measurements
establish that the fallback does not recover an answer within the 10-second limit.

The polynomial-size counter covers both the term limit (normally 4096) and the
monomial degree safeguard (1024), so it does not identify which sublimit fired.
The matrix counter similarly covers several storage/dimension safeguards.

| Group | Cases | Reference answer | Observed Z3 blockage |
| --- | ---: | --- | --- |
| Nonlinear systems over F211 | 13 | UNSAT | 9 work limits, 3 matrix limits, 1 polynomial-size limit |
| Small-field witness problems | 4 | SAT | All four hit matrix limits after any initial sparse probes |
| 64-bit arithmetic-shift determinism, encoded over a large field | 1 | UNSAT | Polynomial-size safeguard during expansion |
| Large-field translation-validation query | 1 | SAT | Polynomial-size safeguard during expansion |

The high-budget algebra-only diagnostics observe matrix-limit failures on six
additional cases that first hit the default work budget. Three other work-limited
cases reach the 2-second diagnostic timeout; this does not establish whether a
longer run would finish. The existing size-limited cases remain size-limited.
Merely increasing the algebra operation allowance is therefore insufficient for
most of this set.

## Interpretation

The dominant measured gap is scalability of polynomial construction and basis
reduction. The retained bit-domain and interval rules exploit Boolean circuit
structure; they do not make these arbitrary nonlinear systems substantially
smaller. cvc5's inspected implementation delegates basis computation to CoCoA,
while its split solver also separates and exchanges algebraic consequences.
The successful cvc5 results establish an advantage on these inputs, but these
Z3-side counters do not identify the particular CoCoA heuristic responsible.

In particular, the four small-field SAT cases cannot currently be attributed
primarily to weak model search: the matrix cap blocks the ordinary algebraic
path first. Better witnesses may bypass that cost, but the round-6 probes did
not recover these cases. Likewise, the exact reason cvc5 split succeeds on the
64-bit shift remains an architectural hypothesis; the directly measured Z3
failure is polynomial expansion.

The next measured priorities are managing matrix/degree growth and preserving
compact circuit definitions through algebraic encoding. Generic witness search
is a complementary direction. The existing bounded packed-row and split-prepass
prototypes did not close these gaps and remain disabled by default.

## Per-input diagnostics

| Input | cvc5 answer | Default Z3 algebra limit |
| --- | --- | --- |
| `deterministic_bvashr_64.smt2` | unsat | polynomial size |
| `i_211_8_16_system09.smt2` | unsat | work |
| `i_211_8_16_system08.smt2` | unsat | matrix |
| `i_211_8_16_system07.smt2` | unsat | work |
| `i_211_8_16_system14.smt2` | unsat | work |
| `i_211_8_16_system22.smt2` | unsat | work |
| `i_211_8_4_system12.smt2` | sat | matrix |
| `i_211_8_16_system15.smt2` | unsat | work |
| `i_211_8_16_system10.smt2` | unsat | polynomial size |
| `i_211_8_4_system07.smt2` | sat | matrix |
| `r_13_32_16_system07.smt2` | sat | matrix |
| `i_211_8_16_system24.smt2` | unsat | matrix |
| `i_211_8_16_system17.smt2` | unsat | work |
| `i_211_8_16_system05.smt2` | unsat | work |
| `i_211_8_16_system01.smt2` | unsat | matrix |
| `i_211_8_16_system18.smt2` | unsat | work |
| `i_211_8_16_system00.smt2` | unsat | work |
| `i_211_8_4_system21.smt2` | sat | matrix |
| `compilation-deterministic-random-06v-016t-ff-zokref-255b-0s.smt2` | sat | polynomial size |

Raw statistics and commands are in `tests/finite_field/results/performance-round6/gap-diagnostics.json` and `diagnose_gaps.py`.
