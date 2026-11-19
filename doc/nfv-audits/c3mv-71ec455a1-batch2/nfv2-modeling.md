# Continuous c3mv NFV audit: batch 2 modeling handoff

## Stage result

Modeling is complete for the seven previously selected whole properties P11-P17.
All seven resolve with trusted Dafny 4.11.0. No property-free validity, concrete
domain, original positive property, or whole-negation verification has run yet.
Resolution is not a proof, a refutation, or a native solver/crash test.

The current provenance check passes: 171 exact source tags, nine pinned source
files, and 17 disclosed body-defined helpers. Source tags establish quotation
provenance, not semantic equivalence. This remains a manual local audit, not an
official hosted NFV driver result; upstream parser/extractor/admission gates have
not been run. No production source was executed, compiled, imported, or changed.

Source remains pinned to `71ec455a18702fe695d0c924a535ff9f385bd58d`, relative to
master `d738f81eab9af1468394664a812fe4310ae8e1fa` and merge base
`437536cd64a544a1c329fc57d83e56e294fdf47c`. Checkout remained clean on `c3mv`
at published audit commit `69b9548ea0b4fad73762f95d5633b21571706d70`.

## Artifacts and evidence

All paths below are relative to the session `files` directory.

- `make_nfv2_models.py`: deterministic seven-model and metadata generator.
- `check_nfv2_models.py`: retains draft inputs and full provenance/resolve logs.
- `nfv2-models`: canonical models, `properties.json`, pinned `sources.json`.
- `nfv2-models/drafts`: both check rounds, including the failed first provenance
  check and every exact resolver input/log; 16 checks in `draft-checks.json`.
- `nfv2-models/provenance.json`: successful final metadata/provenance check.
- `freeze_nfv2_models.py`, `nfv2-model-freeze.json`, `nfv2-models/frozen`:
  exact pre-verification modeling baseline, contracts, and hashes.

The first provenance failure concerned two structural `else` lines incorrectly
marked synthetic. They were corrected to source tags. Both rounds' seven
resolution checks succeeded; there were no syntax/type errors. P11 emitted the
visible missing-quantifier-trigger warning in both rounds. It was not suppressed
with an attribute; `--allow-warnings` preserves it in the logs. All final model
bytes exactly match their most recent successful resolver inputs. Python tooling
parses, helper contract metadata is complete, and every concrete witness names
exactly the entry's inputs. Witness shape checking is not a domain proof.

Frozen selection SHA-256:
`be379560dc9f91cc8650d5abaa0de4e4680748d54c81be5385cc69e2131a1685`.
Canonical metadata SHA-256:
`3f17fef439dfc292ce3d2b9b8a9f6bae0afddd50e490671307f0efbb8900eb97`.
Pinned source JSON SHA-256:
`fbbcd435f1123dabe550a150a49f526031f06c902b470fe4002a752523e0658c`.

| Model | Canonical SHA-256 |
| --- | --- |
| P11 | 0789716ac724f28d39e1c0c58b845fa2859990e477060e759d3c7f9b91c9655f |
| P12 | 19015a7d10d897082a65cc72ebb18d2733a1d2458a7bdbb71ed7232b5c59ca5e |
| P13 | c3e4eb7b9e9c66590d777e2c131c27d032ac708c0edd1badd0bd7fd8e53d2184 |
| P14 | afd2ca8f144677df88bd60989ef8841520b8f746d3e85f28866e4cf4cce126cc |
| P15 | cb152e72f57a5e16f666399b6b51572ba59200d92b4e01d04095f758aea281fe |
| P16 | b84a7d058897d56d2f41760190af873379e4080bbbc0ef96da218a43158a8c99 |
| P17 | 3bfb9c68d2569c52792c06ff1c542bd281573030f46061d821a0f111f7d07035 |

## Translation decisions and limits

P11 retains the identity/unit comparison and the sole fixed-shape alignment
window for the full-discharge branch, distinct from batch-1 prefix pruning.
Opaque AST identities are distinct while their word valuations can overlap or
be empty. The interpreted infix helper is a body-defined observation, not an
assumed containment oracle. Native caller reachability is still unproved.

P12 models the actual unsigned multiply/add guard with modulo 2^32, not
mathematical overflow-free arithmetic. Its selected potential witness is only a
scalar pattern length; no giant literal was allocated and no allocation/native
reachability claim follows. Its scope is case admission, not replacement
semantics, complete case iteration, or allocator behavior.

P13 retains scan/erase/same-index continuation and head adjustment. The whole
contract covers first conflict, stable retained queue, head update, and head
bounds together. Queue predicates and recursive specification functions have
bodies. Per-request equality observations and kinds are immutable input data,
not an assumed proof of regex equivalence. Status/trail/statistics side effects
are explicitly outside this selected value-level transition model.

P14 expands the selected regex branches into their membership semantics for
epsilon/singleton observations. It includes fixed index 0..64 and last index,
including empty/out-of-range `str.at`. It does not verify the general compiler
or recursive regex engine. The P11 interpreted-word length bounds (two clauses)
and P14 word-length bound are marked OPTIONAL EXTRA restrictions, not native
source guards. Retain the frozen contracts in original/candidate checks; if a
refutation is accepted, run and record a separate restriction-removal follow-up.

P15 preserves the actual first-only replacement, including empty needle,
no match, and later copied characters. The source helper loops are represented
by structurally decreasing pure recursion with the same guards/state/order so
the replacement observation can occur in an entry postcondition. `MatchFrom`
has a body and an equivalence contract; `ScanPreserves` is a disclosed erased
proof lemma with a body. Neither contract is trusted: the validity stage must
verify both. The integer/numeric-domain abstraction is conditional; native
allocation, aliasing, graph blocking, marks, and lifetimes are not modeled.

P16 actually erases by shifting left/pop, then restores using append/backwards
shift/saved-slot assignment. It never sets the result equal to the original to
make the property tautological. Modeled sequence accesses must prove safe.
Integer values abstract movable records; no destructor/allocator/refcount/native
memory safety or complete dependency/substitution pipeline claim is made.

P17 retains the tri-valued fold, identity, decisive short-circuit, and unknown
accumulation. Empty lists generalize the fold identity without a claim that a
native AST has that arity. Recursive truth, budgets, derivative/slicing logic,
and regex witness construction are not covered by this property.

## Next scheduled stage: nfv2-verify

Do only verification in the next scheduled stage, not publication. First read
the frozen selection and modeling baseline. Reuse the published runner/checker
against `nfv2-models`, NEVER the original batch-1 model directory. Use the pinned
Dafny executable and explicitly bundled Z3 4.12.1, two cores, and bounded
assertion limits; retain every input, command, full log, timeout, and failure.

Verify property-free validity and independent concrete domains first. All helper
contracts/body proofs must be checked, not assumed. Then attempt each ORIGINAL
COMPLETE positive property. Failed proofs/timeouts are not refutations. P11 and
P12 have only candidate witnesses: a refutation needs the mechanically negated
whole conjunction, EVERY input independently pinned, and a checked concrete
caller. Use no assumes, axioms, bodyless helpers, verifier attributes, or other
trust escapes. Preserve the quantifier warning; optional `O:smt.mbqi=true` is a
documented sound solver option, not a way to turn an unresolved check into a
verdict.

The exact modeling baseline is sealed before any property check. Entry and
non-proof helper computation, helper contracts, and entire original contracts
must not change in response to proof results. Sound proof annotations/erased
proof bodies may be engineered, compared explicitly against the frozen inputs,
and disclosed with exact checks. A repair experiment may change ENTRY
computation only, keeping helper/input contracts and the entire original goal.
Do not silently regenerate over proof engineering or relabel a repaired model
as the original. No production patch or native execution is authorized by this
methodology stage.

After verification, publication must use a NEW batch-2 report directory with
this baseline, selection/coverage, source follow-up, and all check histories.
Continuous schedule #2 remains active at 10-second intervals. Finish each
bounded stage before the next, publish substantive batches, and enqueue genuine
remaining coverage rather than stopping or manufacturing findings.
