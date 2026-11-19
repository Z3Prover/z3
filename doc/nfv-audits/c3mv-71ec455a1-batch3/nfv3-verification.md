# Batch 3 verification handoff

Status: bounded verification stage complete. **One whole translated local
contract refuted; one whole translated property resource-exhausted.** No new
native solver bug, false SAT/UNSAT result, crash or compiled repair is claimed.
The next separate stage publishes these results and enqueues genuine remaining
work. Keep continuous schedule 2 active.

Source pin: `71ec455a18702fe695d0c924a535ff9f385bd58d`.
Master pin: `c2460a558fc6fee3cf15cfebd2d3f642ebf77770`.
Latest remote observation: c3mv remains
`146f70d7ddf5507fdf731af2511edf4c5f669fc5`; master remains the comparison pin.
The worktree is clean. No source was executed, built, imported or patched.

## Accepted outcomes

**P18, complete power-trichotomy rewrite identity: resources_exhausted.**
Property-free validity (003), all eight independent domains (005), and
constraints_ok for all eight concrete branch samples (007) pass with explicit
MBQI. Thus the intended implication is not merely vacuous on the chosen
examples. The original complete word-equality proof (008) times out at the
30-second assertion-batch limit: nine verified, zero errors, one timeout.
The original goal, helpers, assumptions and all five cases are preserved.
No scalar-length replacement, assumed word theorem or counterexample claim.
The missing-quantifier-trigger warning remains visible in raw logs; no trigger
or other verifier attributes were added. Default validity attempt 001 failed
to establish two indices; sound supplemental MBQI resolved them in 003.

**P19, documented rewatch return contract plus complete local watch updates:
refuted, missed-hit/performance classification only.** Property-free validity
002/011 and independent concrete domains 006 pass. Original full positive
proof 009 fails, which alone is not refutation. Attempts 010 and 012 also
fail to prove the pinned negative goal and are retained as failures.

Accepted full refutation is **013**, with twelve verified and zero errors.
It mechanically negates the entire original conjunction represented by
WholeRewatch, pins every one of the eight independent inputs, and checks a
concrete caller with explicitly proved current-watch semantic membership.
Only a visited-prefix physical-membership loop invariant was added to the
original model; computation, helper contracts, entry domains, whole positive
goal and all original examples remained frozen. The accepted attempt uses
explicit smt.mbqi=true. This is not a negative result inferred from a failed
positive proof.

The witness has lits=[0,1], canonicalPointers=[0,1],
pointeeValue=[10,20,10,20], activePointers=[2,3], oldWatch=0, coreIdx=0,
bucketWidths=[1,0], bucketItems=[0]. Both semantic classes are active through
distinct live aliases, while neither canonical pointer identity is active.
The source identity test therefore can return moved despite no semantic core
literal being absent. That is a local documented-converse/missed-hit issue;
it is NOT a proof of an invalid unsat core or a false solver answer.

## Required bounded follow-ups

014 proves `!moved || HasAbsent(lits,canonicalPointers,pointeeValue,activePointers)`
as a strictly shorter consequence of the entire original positive property,
with all twelve inputs AND outputs free and no witness pins. 015 independently
refutes that consequence on the original witness and frozen computation.
There are no optional entry restrictions, so restriction-removal follow-up is
not applicable; none was silently retained as necessary for refutation.

The entry-only candidate changes the existing identity guard to the existing
SemanticActive helper and adapts only its proof invariant. Helpers, all entry
requires and the original whole positive goal are byte-identical. Candidate
validity 016, all three domains including the original witness 017, and the
general complete original property 018 pass. This is a translated-model repair
only: no C++ edit, compiled test, native cache-hit measurement or end-to-end
solver/core-soundness claim. The exact candidate is P19-candidate.dfy.

## Complete attempt ledger

Eighteen verification invocations: twelve successful, six unsuccessful,
including one timeout. This is separate from the three successful modeling
provenance/resolve checks and the final local provenance validation.

| Attempt | Check | Result |
| --- | --- | --- |
| 001 | P18 original property-free validity | 2 unproved index obligations |
| 002 | P19 original property-free validity | pass |
| 003 | P18 MBQI validity | pass; trigger warning retained |
| 004 | P19 initial independent domains | 3 unproved existential premises |
| 005 | P18 MBQI independent domains, 8 callers | pass |
| 006 | P19 domains with explicit existential witnesses, 3 callers | pass |
| 007 | P18 all 8 concrete branch admissions | pass |
| 008 | P18 complete original property | 30-second timeout |
| 009 | P19 complete original property | 2 unproved postconditions |
| 010 | P19 initial complete pinned refutation | unproved postcondition |
| 011 | P19 proof-invariant validity | pass |
| 012 | P19 complete pinned refutation with invariant | unproved postcondition |
| 013 | P19 complete pinned refutation with invariant and MBQI | pass |
| 014 | P19 shorter consequence, all inputs/outputs free | pass |
| 015 | P19 independent shorter refutation | pass |
| 016 | P19 entry-only candidate validity | pass |
| 017 | P19 candidate independent domains | pass |
| 018 | P19 candidate complete original property | pass |

Every exact checked input and full unabridged log is under
nfv3-models\checks, indexed with commands, times, exit codes, hashes and MBQI
settings in checks.json. Every invocation explicitly used Dafny 4.11.0 with
bundled Z3 4.12.1, two cores, 30 seconds per assertion batch, --allow-warnings
and --show-snippets false. No inspected native Z3 executable was run.

validate_nfv3_verification.py checks raw input/log/frozen hashes, unchanged
computation/contracts, complete eight-input pins, mechanical full negation,
the free-input/output implication, exact candidate-only deltas, syntax and
final provenance. Results are in nfv3-results.json, with follow-up details in
nfv3-followups.json and exact proof-only hash changes in annotations.json.
Provenance is not translation equivalence or full upstream admission gates.

## Publication stage requirements

Publish a distinct batch-3 directory with this result, all exact evidence,
frozen selection/models, tools, complete metadata, and the earlier batch-3
P12 source applicability plus C10/C11/C12 coverage handoffs. Preserve earlier
published evidence and their original master pin. Preserve the two recorded
pre-freeze source-selection/coverage validation corrections as non-verifier
events, not solver findings. Keep old source/master references distinguishable.

Use portable replay/publication validators, LF-stable hashes and raw indexed
Git-byte checks. Commit only the new audit directory, include both required
trailers, push without force and independently verify the server SHA. The
latest remote observation is unchanged, but recheck safely before committing.
Do not checkout, pull/rebase, change stash or touch unrelated user files.

After publication enqueue another coverage-driven batch, not another identical
proof run: e.g. bounded producer-wise C11 acyclicity analysis or genuinely new
proof-scaffolding work on the unresolved complete P18/P13 goals. Semantic cache
core sufficiency and P12 giant-pattern native allocation/reachability remain
open. Neither a published batch nor the current bounded proof gap completes
the continuous user request. Keep schedule 2 running.
