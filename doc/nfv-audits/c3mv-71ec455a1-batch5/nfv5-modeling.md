# Batch 5: same-intent translation revision, modeling checkpoint

Three revised models and all thirteen typed concrete domain drivers resolve.
Seven construction checks passed: one provenance check and six model/driver
resolve checks. **ZERO verifier, domain-admission or refutation attempts** have
run. Resolution did not catch batch4's lambda-definedness errors; it must not
be mistaken for validity here either. Warnings remain in exact logs.

This is a new translation revision of the SAME P20/P21/P22 whole-entry intents,
not three new source properties or new audit coverage. Source remains
`71ec455a18702fe695d0c924a535ff9f385bd58d`; master remains
`c2460a558fc6fee3cf15cfebd2d3f642ebf77770`. Baseline publication is
`f975e94d9830bcca332b309df422b364c6e99191`. Batch4's sealed files, failed checks
and published report remain untouched and authoritative for that revision.

The revision plan was frozen BEFORE generating any new model:
`nfv5-retranslation-plan.json`, SHA-256
`c39fc8ff35ceffc30a16b50b4fbcea03f9a72b50dcc00a40e26bac179a975ae5`.
Its separate freeze receipt is SHA-256
`7d5357ee217fe4e753187e4e8ffad4ae4ff794b3102975907287de0a3710110a`.
The original source-intent selection remains SHA-256
`7d7e9ff5bc259460e5dfc9b6892f7ccadc1fd8378fd10e970a585b07029bb4ce`.

## Exact translation change

Five helper-body lines change: `Widths` in all three files, plus `Deactivate`
and `Rebase` in P20. Raw `rows[i]`/`active[i]` indexing inside their sequence-
constructor lambdas becomes existing total `R(rows,i)`/`B(active,i)` access.
No helper is added, skipped or given a new contract. Every entry method,
including its complete body and contracts, is byte-identical to the baseline.
`nfv5-retranslation-diff.json` retains the exact before/after hashes and diffs;
`nfv5-models\baseline` retains the original model bytes/metadata for independent
comparison. This is disclosed translation computation revision, NOT an
annotation-only edit or an entry-only source-bug repair.

For constructor indices0<=i<n, R returns the original row and B the original
boolean. Length remains n. Thus the intended values at evaluated indices are
retained; outside-domain lambda arguments use existing empty/false defaults.
This is a definitional scoped mathematical argument, not a proof obtained by
assuming the invalid old model or a C++/Dafny correspondence theorem. Whether
the NEW models pass all well-definedness obligations is left to the next stage.

All45 named input parameters, all14 original mandatory requires clauses,
all19 outputs, three COMPLETE original ensures per entry, all62 helper
signatures/contracts/environment metadata and thirteen input examples remain
unchanged. No optional restrictions exist. Metadata adds only the new raw
hash and an explicit revision record. No mutable-current-base DAG precondition,
unsat oracle, exact-transition weakening, new bound or guessed result was added.

P20 still models complete deactivation/registration/rebasing and an unbounded
finite-cycle predicate. P21 still distinguishes fixed background from temporary
query premises and recomputes finite-language intersection. P22 still models
canonical clones, aliases, full ownership/ID effects and low32 hash collisions.
Existing successful-allocation, mathematical row/tuple, finite-language and
hashtable ADT abstractions remain. Local source tags establish provenance, not
full upstream extraction/admission or translation equivalence. No native source
was executed, built, imported or patched.

## Seal and separate verification stage

`nfv5-model-freeze.json` seals new models, typed drivers, full metadata,
source inventory, exact baseline copies, construction history and tooling.
Every changed line is checked against the pre-frozen edit allowlist; every
entry body/contract is independently compared with the baseline. Original
requires/goals/helper contracts and computation fingerprints are retained.
No further computation or contract edits are permitted after this seal; only
sound, disclosed proof annotations may change. Exact-transition conjuncts
cannot be removed to manufacture a repair.

Next separate scheduled stage is `nfv5-verify`: property-free validity FIRST,
then independent domain admission, then entire originals. Use pinned
Dafny4.11/Z3 4.12.1, two cores and30-second obligation limits; preserve every
failure/warning/timeout. An accepted refutation still needs all input pins,
mechanical negation of the ENTIRE conjunction and an independent checked
caller. No refutation or native bug is established here. P13/P18 and native
reachability of the gpower/cache hypotheses remain open. Schedule2 stays active.
