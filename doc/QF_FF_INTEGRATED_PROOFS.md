# Integrated finite-field proofs (working branch)

With `:produce-proofs true`, finite-field conflicts now carry replayable PAC
evidence in ordinary Z3 proofs. The field algebra and evidence recorder live
under `src/math/ff` and `src/ast/ff`; the classic SMT and SAT/EUF adapters
only supply their assigned field literals and retain the scoped proof hints.
The proof-aware finite-field simplifier supplies local proofs for its Boolean
circuit and field rewrites. The ordinary `check-sat`/`get-proof` path does not
require the standalone `ff-certify` command.

For pure ground QF_FF, `(ff-check-native-proof)` checks a previous UNSAT
result against the current assertions. It rejects open hypotheses, unsupported
proof families and rules, and failed field or rewrite obligations. The command
checks Z3's proof internally; it is not an independent checker. The separate
`scripts/ff_native_alethe.py` exporter attempts to elaborate the same native
proof into an original-input Alethe proof with PAC leaves, checked by Carcara
and FFPacheck. It fails closed when it cannot export or check a proof.

The native proof regression tests cover field contradictions, SAT candidates,
preprocessing and circuit rewrites, theory combination, SAT/EUF scopes and
assumptions, proof-clause weakening, and malformed evidence. A focused external
test checked three field leaves and 32 whole native proofs with Carcara and
FFPacheck. The PR2 certificate command and its independent pipeline remain
available for comparison.

## FMCAD screen

The 390 distinct FMCAD26 `FF_UNSAT_SMT` inputs were run with 10 seconds per
input and four workers on 2026-10-15. The native checker run and the external
export run used the same input files and built library. The historical PR2 row
comes from the post-merge native/circuits run on 2026-10-14; it was not rerun
with this branch. The new lightweight runners did not enforce PR2's sampled
16 GiB process-tree RSS cap, so these counts are a coverage screen rather than
a controlled speed comparison. All counts below require successful checking,
not merely a solver UNSAT answer.

| Pipeline | Checked / 390 | Meaning |
| --- | ---: | --- |
| PR2 native/circuits | 377 | Original-input Alethe/PAC checked by Carcara and FFPacheck |
| Integrated native proof | 351 | Original assertions to contradiction replayed by Z3's native proof checker |
| Integrated Alethe export | 284 | Native whole proof independently checked by Carcara and FFPacheck |

The integrated native checker succeeds on one input PR2 did not check, and
misses 27 that PR2 checked. The external export checks a subset of 284 of the
351 native successes; 67 native proofs do not finish external export/checking
within this profile. The external run has 39 solver non-UNSAT results (mostly
timeouts), 40 external-stage timeouts, nine Alethe size-limit failures, five
retained-term-limit failures, three token-limit failures, and a few other
budget failures. These are incomplete certificates, not accepted UNSAT proofs.

This branch therefore demonstrates integrated proof recording and checking,
but the external coverage is below PR2's current pipeline. The main remaining
work is to record the shared solver's preprocessing and circuit consequences
at their source, avoiding a second, larger polynomial encoding, and to reduce
the cost of elaborating native Boolean proof steps into Alethe. SAT/EUF root
splitting also needs to use upstream's common field-lemma implementation; the
SAT/EUF adapter currently omits that optional heuristic.
