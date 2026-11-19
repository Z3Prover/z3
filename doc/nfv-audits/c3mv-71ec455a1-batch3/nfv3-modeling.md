# Batch 3 model-construction handoff

Status: P18 and P19 drafted, exact source-tag/metadata checks passed, and both
Dafny files resolved. This stage does not verify well-definedness, discharge
any helper contract, prove either whole property, or establish a refutation.
Do not count resolve success as a verified property or an independent domain.

The immutable selected intent hash is
`0beb5b435b99a07ee85fbc6830028ee477f8b79bbd243c1f254887ef9b0da13e`.
Source remains `71ec455a18702fe695d0c924a535ff9f385bd58d`, with master pin
`c2460a558fc6fee3cf15cfebd2d3f642ebf77770`. No production code was executed,
built, imported, changed or patched. No native solver run occurred.

## Models

`nfv3-models\P18.dfy`: all five power-trichotomy apply cases and both
directions, with complete residual words and conditional equality goal.
Its 19 explicit inputs include all fresh valuations, both token-boundary
views and literal-classification observations. Eight helpers define truncated
signed word power, token-view shape, actual partial literal accumulation,
period scanning, primitive-root search, unsigned-32 arithmetic and enumerator
applicability. Fresh exponent k and N remain signed; no empty-root exclusion
or assumed common-root theorem was added. Side conditions are an output
conjunction, not an always-true oracle. Directional lengths use word powers,
not invalid negative-count length products. The source word/one/cat helpers
are inlined as direct sequence slices and concatenations.

`nfv3-models\P19.dfy`: identity-based rewatch loop, skip-old-watch behavior,
complete unwatch/update/watch state mutation, and the original whole documented
semantic-presence/state-update contract. Nine helpers define pointer tables,
semantic presence, identity membership, bucket representation, first removal,
exact unwatch/watch, semantic absence and the complete positive conjunction.
Watch buckets are represented by their lengths and concatenated contents,
including missing-bucket growth and preservation of row order. No semantic
membership test replaces the actual identity test in the implementation.

The models remain semantic projections under explicit input observations,
not C++/Dafny equivalence or native safety proofs. AST construction/rewriting,
dependency provenance, freshness/lifetime, global scheduling/reachability,
allocation/capacity/overflow effects and full cache core soundness remain
outside the respective goals and disclosed in metadata/frozen selection.
The literal flags are observations of syntax, never inferred from valuation.

## Exact checks and freeze

`make_nfv3_models.py` generates the two draft files and full per-requires/helper
metadata. `check_nfv3_provenance.py` checks exact immutable source tags,
metadata, forbidden constructs and unchanged complete ensures. It does NOT run
the upstream extractor/parser/span/admission gates or prove source fidelity.
`check_nfv3_models.py` preserves exact inputs and all diagnostics under drafts.

Three draft checks: one provenance pass and two resolve passes, all successful.
Exact snapshots, commands, timestamps, logs and SHA-256 values are retained in
`nfv3-models\draft-checks.json` and `drafts`. No warning was suppressed; raw
logs are authoritative. There are zero Dafny verification attempts so far.

`freeze_nfv3_models.py` seals raw baselines under `nfv3-models\frozen` and
records file hashes plus computation/contract fingerprints in
`nfv3-model-freeze.json`. Do not regenerate or overwrite sealed files. Future
proof annotations may not change computation, helper contracts, entry domains,
the complete original positive goals, or the eleven original domain examples.

## Next stage: nfv3-verify

First verify property-free validity for each frozen model, removing only the
entry ensures. This still checks helper bodies/contracts and all index/domain
obligations. Repair failures only with sound proof annotations after freeze;
otherwise report invalid/unresolved translation rather than weakening a goal.
Next independently check the frozen concrete input domains. For P18, also
establish constraints_ok on the eight selected case examples so that the
conditional goal is demonstrably non-vacuous on these domains. Such admission
checks do not replace the complete equality goal. For P19, verify pointer and
bucket representation plus the current-watch semantic-presence premise.

Then verify each complete original positive property using pinned Dafny 4.11.0
and explicitly selected bundled Z3 4.12.1, two cores, 30 seconds per assertion
batch, --allow-warnings and --show-snippets false. Preserve every exact input,
log, failure, resource result and warning. No native audited Z3 execution.

If P18 lacks a word-algebra proof, keep its whole goal unresolved; do not
replace it by lengths or assume root/period identities. If P19 fails, that is
not itself refutation: mechanically negate its complete conjunction, pin
every input independently, prove the candidate domain and a concrete caller.
An accepted alias-pattern refutation is only a missed-hit/control-contract
result, not a native false SAT/UNSAT result, semantic-core proof or crash.
Follow the prescribed bounded implication/shorter-property and model-entry
candidate-repair protocol for any accepted refutation without editing C++.

Preserve P13's complete queue proof gap, C11 caller acyclicity and semantic
cache-core sufficiency as unresolved. Keep schedule 2 active. Publish only
after the distinct verification and publication stages, preserving both old
reports/evidence histories and the user's stash.
