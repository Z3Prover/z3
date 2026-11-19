# Continuous c3mv NFV audit: batch 2 verification handoff

## Stage result

Verification is complete as a bounded audit stage: **four whole translated
properties verified, two conditionally refuted, and one unresolved**. This is
not seven successes, not a proof of native C++ correctness, and not a native
solver-result or crash finding. No inspected production source was executed,
built, imported, or modified. Publication is the NEXT scheduled stage.

All seven current models pass property-free validity and independent concrete
domain checks. Full positive properties were attempted only after those checks.
Only proof annotations changed from the sealed modeling baseline; computation,
entry/helper contracts, input domains, and original complete goals are unchanged.
`refresh_nfv2_proof_metadata.py` checks this against the exact frozen files.
This is a line-oriented check plus inspected edits, not a general Dafny parser
or a replacement for the unrun upstream translation/admission gates.

`nfv2-results.json` is the machine-readable result/evidence ledger, SHA-256
`911cd61fbfe11f0aacbcac03deefab9d058bef88d12b3ab63adadf30702ce7ad`.
Pinned source remains `71ec455a18702fe695d0c924a535ff9f385bd58d`; master and
merge base are unchanged from selection. Local `c3mv` remained clean at
`69b9548ea0b4fad73762f95d5633b21571706d70`; the stash was not touched.

## Complete-property results

| ID | Whole selected property / outcome | Primary exact checked input under `nfv2-models\checks` |
| --- | --- | --- |
| P11 | Full-discharge preservation: REFUTED translated model | `030-P11-annotation-refute.dfy` |
| P12 | Unsigned replacement-case admission equals mathematical range: REFUTED translated model | `022-P12-refute.dfy` |
| P13 | Request conflict, stable queue, head update and head bounds: UNRESOLVED complete proof | `031-P13-proof.dfy` |
| P14 | Selected `str.at` preimage membership equivalence: VERIFIED translated model | `018-P14-proof.dfy` |
| P15 | Character observation preserved by first replacement when absent from both operands: VERIFIED translated model | `019-P15-proof.dfy` |
| P16 | Erase-trail restoration equals original sequence, with modeled accesses checked: VERIFIED translated model | `032-P16-proof.dfy` |
| P17 | Complete tri-valued conjunction/disjunction fold: VERIFIED translated model | `020-P17-proof.dfy` |

P13 has six verifier units discharged and two unproved postcondition obligations
in its full-property attempt. These are NOT six successful selected properties.
The conflict/queue relation needs additional relational proof infrastructure.
Initial relational loop invariants were not established and were removed during
proof engineering; they were NOT removed from the entry's whole positive goal.
Validity, helper domains and independent concrete callers subsequently passed.
There is no P13 counterexample or refutation claim. Preserve this explicit
proof gap rather than replacing the selected property by bounds-only safety.
Its NFV outcome category is `audit_failure`, specifically unresolved proof
obligations, not a syntax/type error, native bug, or resource timeout.

## P11: full discharge extends the existing token-boundary concern

The distinct branch is `ncontains_propagation::propagate:264-291`, with haystack
tokens `[X,unit(a),Y]` and needle tokens `[X,unit(b),Z]`. Identities X/Y/Z are
distinct opaque non-unit ASTs; valuations may nevertheless be short or empty.
The sole token alignment matches X, then finds distinct resolved unit a/b and
returns mismatch. The full-discharge branch removes the negative containment.

Every-input witness: `X=[97,97]`, `Y=[98]`, `Z=[]`, `a=97`, `b=98`.
Interpreted haystack is `aaab`, needle `aab`, with an occurrence at character
offset one. The complete property is
`!discharged || !WordContains(X + [a] + Y, X + [b] + Z)`.
The mechanically negated entire property, all five independent pins, and a
concrete caller verify: **4 verified, 0 errors** in check 030.

The original positive attempt failed (016); a first negative attempt could not
instantiate the infix witness (021). Supplemental MBQI timed out at 30 seconds
(023). A general, proved offset-one implication was then added as a proof-only
annotation, validity/domain were rechecked (024/027), and default verification
accepted the full refutation (030). The visible quantifier-trigger warning is
retained; no trigger attribute, assumption, or suppressed obligation was added.

Both optional interpreted-word length bounds were deleted in separate checks:
validity 033, domain 034, and full refutation 035 all pass. A strictly shorter
consequence, `!discharged || X + [a] + Y != [a] + X + [b] + Z`, is proved implied
with ALL inputs AND the output free (036), then separately refuted on the same
witness (037). No global minimality claim is made.

This extends batch-1 P1's **same token-versus-character root-cause concern** to
full discharge; do not count it as an independently confirmed native bug. The
batch-1 candidate guarded only prefix pruning and did not protect this branch.
The source trace from the earlier continuation stage remains essential: earlier
word equalities can substitute concrete words before the branch. Explicitly
asserting X="aa" or Z="" is not a justified native reproduction of this symbolic
state. No full-discharge production repair was applied or generally proved.

## P12: unsigned guard arithmetic, conditional on a large pattern domain

The admission prelude of `replace_all_split::apply_case:215-229` evaluates
`c >= 2 * p.length() + 2` using unsigned 32-bit arithmetic. Model helper
`Unsigned32` keeps both multiply/add wrapping effects rather than assuming them
away. Frozen mathematical intent is
`admitted == (case_number < 2 * pattern_length + 2)`.

Every-input witness: `pattern_length=2147483647`, `case_number=1`. The true
mathematical threshold is 4294967296; its source-width result is zero. Admission
is false although the mathematical-range hypothesis admits case 1. Original
positive proof 017 fails; independently checked domain 011 and mechanically
negated full-property proof/caller 022 pass (**3 verified, 0 errors**).

There are no optional P12 restrictions. The strictly shorter false-rejection
consequence `case_number >= 2 * pattern_length + 2 || admitted` is proved with
both inputs and the output free (038), then refuted on the original witness
(039). The witness is scalar: no multi-gigabyte literal was allocated. Actual
literal construction, buffer limits/allocation, caller reachability, and a
native solver failure remain UNPROVED. The result refutes a source-inferred
admission hypothesis on this modeled domain; do not relabel it a native crash.

`P12-candidate.dfy` changes ONLY entry threshold computation to
`2 * pattern_length + 2` in mathematical/nonwrapping arithmetic. All helpers,
input contracts and the entire original property are byte-identical up to the
entry body. Candidate validity 040, original-witness domains 041, and full
general property 042 pass. A sufficiently wide carrier can represent this
domain's threshold, but this is only an ADMISSION-PRELUDE model repair: it does
not prove complete case enumeration, downstream replacement indexing, or an
end-to-end native fix. No C++ patch was made.

## Evidence and tools

- `nfv2-models\checks.json`: 42 exact verification attempts; **32 successful,
  10 unsuccessful**, including one 30-second MBQI timeout. All inputs/logs and
  failed attempts remain intact. Total observed verifier invocation time was
  95.957 seconds; this is audit process data, not a performance benchmark.
- `nfv2-models\draft-checks.json`, `drafts`: the prior modeling stage's 16
  provenance/resolve checks, including 14 resolution calls and one failed
  provenance round. Do not mix these with the 42 verification attempts.
- `nfv2-models\frozen`, `nfv2-model-freeze.json`: exact pre-verification
  baseline, including original contracts and metadata. Current hashes can
  differ ONLY because of documented proof annotations.
- `nfv2-models\provenance.json`: final provenance pass, seven properties,
  171 exact source tags, nine pinned source files and 17 body-defined helpers.
  `modeling-provenance.json` retains the initial successful provenance result.
- `nfv2_followups.py`: reproducible optional-restriction removal, shorter
  implication/refutation, and entry-only candidate construction/checks.
- `validate_nfv2_verification.py`: validates all 42 input hashes/logs, explicit
  solver/limits, full goals and pins, free implication calls, phase ordering,
  candidate edit boundary, unchanged baseline, metadata, and Python syntax.
  Validation passes. It validates this sealed evidence set, not arbitrary future
  appended experiments; rerun experiments in a separate workspace.

The helper/array membership and slice-extensionality changes are proof-only.
P15's recursive matching/replacement definitions and erased proof lemma all
verify with bodies; P16's left erase/backwards restoration computation was not
replaced by the desired answer. Source correspondence, C++ object lifetimes,
native allocations/aliasing, arbitrary regex recursion and resource budgets,
and whole solver correctness remain outside these selected models.

Pinned Dafny 4.11.0 and explicitly selected bundled Z3 4.12.1 were used, at two
cores and 30 seconds per assertion batch; full commands are in each record.
No hosted workflow, external inference service or native audited Z3 invocation
was used. Two non-verifier tooling issues were corrected: displaced source tags
before new proof annotations failed provenance preflight, and an initially
miscounted validator total was replaced by aggregation of actual check records.
Neither is a solver/model finding; the failed preflight issued no Dafny check.

## Next scheduled stage: nfv2-publish

Create a NEW batch-2 report directory, preserving the original report unchanged.
Include this entire seven-property result set, explicit P13 gap, same-root-cause
grouping for P11/P1, P12 reachability limits, candidate scope, all exact inputs
and logs, canonical AND frozen models, provenance, all metadata and tool scripts.
Also include prior `nfv2-p1-source-trace`, full coverage ledger and frozen
selection artifacts. All session handoffs are evidence inputs, not official NFV
hosted-driver output. Adapt hardcoded session paths only in separately authored
publication/replay tooling; do not alter checked inputs or logs.

Use local `* text eol=lf`, hash final text bytes and validate manifest, links,
Python scripts, provenance, raw indexed Git blobs, and runner nonzero failures.
Commit only explicit new audit paths on `c3mv`, include required trailers, push
without force and independently verify the remote SHA. Preserve stash and user
changes. No production source edits/builds/tests are part of this audit.

After publication enqueue the next genuine coverage-driven batch (remaining
source applicability, callbacks/lifetime, substitution/cycles, cache/core,
trichotomy, power slots or length bounds as justified by the ledger), retaining
P13 as unresolved rather than counting a weaker property as its replacement.
Continuous schedule #2 remains ACTIVE at 10-second intervals. Do not stop it.
