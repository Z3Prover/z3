# Integrated finite-field proofs (working branch)

With `:produce-proofs true`, finite-field conflicts now carry replayable PAC
evidence in ordinary Z3 proofs. The field algebra and evidence recorder live
under `src/math/ff` and `src/ast/ff`; the classic SMT and SAT/EUF adapters
only supply their assigned field literals and retain the scoped proof hints.
Each PAC leaf records the signed premises actually used by its derivation.
The native checker recomputes that support from the DAG, and SMT learns only
the corresponding conflict clause. The Alethe exporter removes unused premise
equations from the PAC subproof and discharges the same clause.
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
export run used the same input files and built library. The earlier PR7 run
used the same scripts and settings before premise-support recording. The PR2 row
comes from the post-merge native/circuits run on 2026-10-14; it was not rerun
with this branch. The new lightweight runners did not enforce PR2's sampled
16 GiB process-tree RSS cap, so these counts are a coverage screen rather than
a controlled speed comparison. All counts below require successful checking,
not merely a solver UNSAT answer.

| Pipeline | Checked / 390 | Meaning |
| --- | ---: | --- |
| PR2 native/circuits | 377 | Original-input Alethe/PAC checked by Carcara and FFPacheck |
| Integrated native proof, before support recording | 351 | Original assertions to contradiction replayed by Z3's native proof checker |
| Integrated native proof, with support recording | 353 | Same check with narrower certified field clauses |
| Integrated Alethe export, before support recording | 284 | Native whole proof independently checked by Carcara and FFPacheck |
| Integrated Alethe export, with support recording | 302 | Same independent check, retaining all 284 earlier successes |

The new native run succeeds on one input PR2 did not check and misses 25 PR2
successes. Its 353/390 count is up from 351/390, but the 10-second boundary is
noisy: five previous successes timed out in the four-worker run and all five
passed two isolated reruns. The external run retained every one of the previous
284 checked inputs and added 18, including seven that had hit the Alethe output
size limit. One of its 302 successes is absent from PR2's checked set. The 88
remaining inputs have no accepted whole-proof certificate in this profile:
30 solver non-UNSAT results, 39 external-stage timeouts, ten process timeouts,
and nine checker or output budget failures. These are incomplete certificates,
not accepted UNSAT proofs.

This branch therefore demonstrates integrated proof recording and checking,
but the external coverage remains below PR2's current pipeline. The main remaining
work is to record the shared solver's preprocessing and circuit consequences
at their source, avoiding a second, larger polynomial encoding, and to reduce
the cost of elaborating native Boolean proof steps into Alethe. SAT/EUF root
splitting also needs to use upstream's common field-lemma implementation; the
SAT/EUF adapter currently omits that optional heuristic.
