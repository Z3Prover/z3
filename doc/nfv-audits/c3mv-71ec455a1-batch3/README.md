# c3mv NFV/Dafny audit: batch 3

**One local model contract refuted; one whole property timed out.** The
refutation concerns a possible missed cache hit, not a wrong solver answer.
An entry-only translated repair satisfies the complete original contract.
No native bug, crash or compiled repair is claimed.

This is a manually authored local audit using the pinned NFV/Dafny methodology,
not an official hosted-driver report or a C++/Dafny equivalence proof. Production
source was inspected only as immutable text: no native build, execution, import,
large allocation, sanitizer run or production patch.

## Revision identity

| Input | Immutable revision |
| --- | --- |
| Audited source | `71ec455a18702fe695d0c924a535ff9f385bd58d` |
| Current master comparison | `c2460a558fc6fee3cf15cfebd2d3f642ebf77770` |
| Merge base | `437536cd64a544a1c329fc57d83e56e294fdf47c` |
| NFV methodology | `microsoft/neuro-formal-verification@599726579274cfeb1c0915414b911371527a9870` |
| Previous audit publication | `146f70d7ddf5507fdf731af2511edf4c5f669fc5` |

Master advanced by two commits during source tracing. Earlier batches retain
their original master pin `d738f81eab9af1468394664a812fe4310ae8e1fa`; their
results are not silently relabeled. The merge-base branch delta remains 104
files / 89 src files. The new direct master-to-source comparison has 110 files /
93 src files, including upstream-only changes. The new master paths do not
overlap the nine coverage-capture files, but smt_context.cpp does overlap the
broader branch delta by path. See the [coverage handoff](nfv3-coverage.md).

## Findings and proof gaps

| Property | Entire selected goal | Outcome |
| --- | --- | --- |
| P18 | All five power-trichotomy apply cases, both directions, preserve the emitted word substitution when their actual constraints hold | Resource exhausted: 30-second proof timeout |
| P19 | Documented semantic rewatch return contract **and** complete local watch/bucket updates | Refuted translated contract; missed-hit/performance classification |

### P19: semantic presence and canonical pointer identity diverge

[constraint_store](https://github.com/z3prover/z3/blob/71ec455a18702fe695d0c924a535ff9f385bd58d/src/util/stx_search_tree.h#L575-L613)
interns by pointee equality and owns clones. Active constraints are borrowed live
objects. [try_rewatch](https://github.com/z3prover/z3/blob/71ec455a18702fe695d0c924a535ff9f385bd58d/src/util/stx_search_tree.h#L681-L707)
checks whether canonical pointers occur in the active pointer vector, while its
documented return contract talks about whether core literals are active.

The checked witness uses canonical identities `[0,1]`, semantic classes
`[10,20,10,20]`, active live identities `[2,3]`, core literals `[0,1]`, watch 0,
core ID 0, and buckets with widths `[1,0]` and contents `[0]`. Both semantic
classes are active through distinct aliases, but the canonical identities are
absent. The model can move its watch despite no semantic core literal being
absent. A separate shorter refutation isolates that return-contract failure.

Accepted evidence is [013: full refutation](nfv3-models/checks/013-P19-visited-prefix-mbqi-refute.dfy)
and its [complete log](nfv3-models/checks/013-P19-visited-prefix-mbqi-refute.log):
twelve verified, zero errors. The entire original conjunction is mechanically
negated, every input is independently pinned, and a concrete caller is checked.
A failed positive proof was not treated as refutation. The
[shorter implication](nfv3-models/checks/014-P19-shorter-implied-free-inputs-and-outputs.dfy)
has all inputs **and outputs** free; its
[independent refutation](nfv3-models/checks/015-P19-shorter-refute.dfy) also passes.
There were no optional entry restrictions to remove.

An [entry-only candidate](nfv3-models/P19-candidate.dfy) uses the already-defined
semantic membership helper instead of pointer membership and adapts its proof
invariant. All helpers, input contracts and the full original property remain
unchanged. Candidate validity, all three domains including the original witness,
and the [general whole-property proof](nfv3-models/checks/018-P19-candidate-proof.dfy)
pass. This is a model repair, not a C++ fix or a proof of semantic unsat-core
sufficiency. No false SAT/UNSAT result or native crash follows from this finding.

### P18: full word identity remains unproved

The [model](nfv3-models/P18.dfy) preserves all five apply cases, both directions,
signed/truncated powers, empty fresh roots, negative fresh k, actual constant
period slices, and the enumerator's constant-base commutativity guard. Literal
token status is observed syntax, not inferred from a word valuation. No common
root theorem is assumed. The complete goal is not replaced by scalar lengths.

Property-free validity, eight independent domains, and non-vacuous admission
for all eight selected branch examples pass with explicit MBQI. The
[original whole-property attempt](nfv3-models/checks/008-P18-mbqi-proof.dfy)
[times out](nfv3-models/checks/008-P18-mbqi-proof.log) at the fixed 30-second limit.
This is a resource result, not a refutation. The missing-trigger warning remains
visible; no verifier or trigger attributes were added.

### P12 applicability follow-up and remaining coverage

The [source trace](nfv3-p12-source-trace.md) found no explicit excluding length
cap in the inspected constructors/callers. Holding the giant pattern still has
unproved allocation and native search-reachability premises. Its last required
buffer growth is representable on the selected 64-bit interpretation; the final
backing buffer alone is 8 GiB. If the rejected initial case is reached, VERIFY
uses the configured exit/exception action even in release builds. No giant
allocation or native failure was attempted. This does not upgrade the prior
conditional scalar refutation to a confirmed native bug.

All 24 production substitution broadcasts were enumerated. The global caller
invariant needed for elimination termination remains unproved; no invented fuel
or acyclicity assumption closes it. Semantic sufficiency of dependency-filtered
cache cores and the prior P13 whole queue property also remain unresolved.

## Evidence, provenance and reproducibility

The [frozen selection](nfv3-selection.json) chose two distinct whole entries
before modeling. [Metadata](nfv3-models/properties.json) gives every inferred
requires, body-defined helper, observation, abstraction and omitted effect.
[Frozen models/contracts](nfv3-model-freeze.json), exact source inventories,
three draft provenance/resolve checks, and all eighteen verifier invocations
are included. [Results](nfv3-results.json), the
[complete attempt ledger](nfv3-verification.md), and
[commands/hashes/log index](nfv3-models/checks.json) distinguish twelve successful
checks, six unsuccessful checks and one timeout. Tool validation is counted
separately, never as new audit findings.

Only a visited-prefix proof invariant was added to the original computation.
At publication, the current final-false source tag was corrected from closing
brace 707 to the actual return statement 706; all historical checked files stay
byte-exact. [Correction notes](publication-corrections.json) distinguish the
current annotations from the exact verified inputs. Source tags establish cited
text, not translation equivalence or complete upstream extraction/span gates.

All normal publication text is LF-stable. One exact historical checked Python
provenance input has CRLF; a single-path `-text` attribute preserves its original
bytes rather than invalidating the recorded input hash. See
[export notes](export-notes.json) and the [raw-byte manifest](manifest.json).
Historical authoring tools retain their original session assumptions and are
not the portable replay interface. Source-stage Markdown handoffs preserve
their original paths/pins; relative evidence links in this README are canonical.

Use the official Dafny 4.11.0 distribution and explicitly select its bundled
Z3 4.12.1, not 4.14.1. Every audit check used two cores, a 30-second assertion
limit, retained warnings, and MBQI only where recorded. These commands do not
execute audited native Z3 code:

```powershell
python .\validate_publication.py
python .\replay_checks.py --dafny C:\trusted\dafny\Dafny.exe --solver C:\trusted\dafny\z3\bin\z3-4.12.1.exe --select 009 013 018 --output C:\audit-replay\batch3
```

Replay writes only to a new directory outside the immutable report and returns
failure for an exit-code mismatch even if later checks succeed. Expected
unsuccessful audit checks remain expected unsuccessful checks. Five separate
live tool-validation invocations tested replay and mismatch propagation; their
[results](tool-validation/results.json) are not part of the eighteen-check audit.

This publication is a checkpoint. Continuous coverage-driven work remains
enabled; unresolved goals are neither silently discharged nor repeated as
empty findings merely to keep the schedule busy.
