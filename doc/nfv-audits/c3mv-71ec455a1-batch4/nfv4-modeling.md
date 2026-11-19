# Batch 4: model construction and seal

Source pin `71ec455a18702fe695d0c924a535ff9f385bd58d`; comparison master
`c2460a558fc6fee3cf15cfebd2d3f642ebf77770`. Frozen selection SHA-256:
`7d7e9ff5bc259460e5dfc9b6892f7ccadc1fd8378fd10e970a585b07029bb4ce`.

Three entry models and thirteen concrete domain drivers resolve. This is
parsing/type/name resolution plus local provenance validation, NOT property-
free verification, proved domain admission, original-property verification,
refutation or a native solver run. No outcome/finding count is increased.

| Entry | Inputs | Complete positive conjuncts | Body-defined helpers | Domains |
| --- | --- | --- | --- | --- |
| P20 power substitution | 14 | 3 | 22 | 4 |
| P21 cache insertion | 26 | 3 | 25 | 5 |
| P22 canonical interning | 5 | 3 | 15 | 4 |

P20 retains all original/current-base, activity, exponent, dependency and flag
columns. Source deactivation is first-active; registration is active-key-only
and precedes rebasing of old AND new records. The incoming dependency is
ignored as in the actual signature. The cycle predicate is absence of any
finite directed cycle, expressed directly, not fuel, assumed rank, a direct-
self-only check or an assumed acyclic mutable input. Immutable AST catalog
acyclicity is separate from the mutable current-base implication in the goal.

P21 retains facet eligibility observations, all active contributing fact rows,
null/nonnull dependency handles, real leaf-subset filtering, existing canonical
IDs, complete core rows, watch positions and watch buckets. Language semantics
are explicitly enumerated finite character words on one variable, not an
unsat oracle. Closing certificates recompute the actual proof-position language
intersection under fixed background and a SEPARATE optional temporary length
query. The semantic goal concerns every stored core under fixed background,
not leaf membership or the query-conditional contradiction. Unicode characters
use the source range0..196607; alternative global character modes are outside
this projection. P19 lookup/rewatch behavior is not silently repaired or used
as a guarantee that a stored entry can fire natively.

P22 retains owned and live pointer aliases as arena indices, semantic value
classes, unsigned64 hashes with the source low32 lookup projection, every heap
ID field and canonical ownership order. A miss first creates the clone with
UINT_MAX ID and then assigns the old store size. Hash collisions still require
semantic equality. No convenient lookup result is supplied as a free input.

All three entries keep the complete frozen structural, exact-state-transition
and semantic/class conjunctions. Exact transitions are fully body-defined;
all helper effects are constrained. A repair that changes the exact transition
may not exist under those frozen conjunctions. That is not permission to drop
the exactness conjunct, weaken semantics or alter helper/input contracts.

## Draft checks and disclosures

Twenty checks are preserved: four provenance runs and sixteen Dafny resolve
runs, including three FAILED initial domain-driver resolutions. Empty literal
substitution in quantified assertions was underspecified. Only the harness
was corrected to give EVERY concrete input an explicit typed local; all
thirteen examples retain their original values. The initial P21 indentation
warning and complete diagnostics remain in immutable draft snapshots.

All original entry models resolved immediately. Before sealing, the already
selected unsigned representation conditions were spelled out for P20 input
base widths and P21 facet count. Only the two affected entry/domain pairs were
re-resolved. Per-helper exact source metadata was separately checked without
rerunning unaffected resolve inputs. There are fourteen mandatory entry
requires clauses and no optional restrictions. No original positive goal or
example changed.

Generated source comments and metadata cover every helper and the selected
entry spans. Checks reject missing anchors, unexpected synthetic computation,
missing input pins/metadata, trust escapes, duplicate declarations and contract
drift. These are local checks, NOT the full upstream extractor, parser, span,
admission or translation-equivalence gates.

Array access and row decoding helpers are totalized with zero/false/empty
defaults OUTSIDE the well-formed representation domains. This is disclosed
mathematical encoding, not a native default or safety fix. Entry requires
exclude malformed inputs; no default is an assumed solver verdict. Successful
allocation/trailing, token flatten/concat projection, finite-language semantics
and canonical hashtable-membership ADTs are not native correspondence proofs.

## Sealed artifacts and next stage

`nfv4-models\frozen` holds byte-exact copies of all three models, domain drivers,
properties/source metadata and author/check/seal tools. `nfv4-model-freeze.json`
records raw hashes, computation/contract fingerprints, full original goals,
all helper contracts, selection lineage and every draft-history hash. All raw
checked inputs and logs remain under `nfv4-models\drafts`. A textual annotation-
stripped fingerprint is an additional guard, not a proof that a future edit
is harmless. Do not modify frozen files or old report trees.

Next separate scheduled stage is `nfv4-verify`: property-free validity, all
independent domain drivers, then the COMPLETE originals, using pinned
Dafny4.11/Z3 4.12.1, two cores and bounded limits. Record every exact input/log,
failure, warning and timeout. An accepted negative result requires independent
domain admission, all inputs pinned and a mechanically negated entire original
conjunction with a checked concrete caller. No negative result is established
at this modeling checkpoint. P13/P18 remain open. Schedule2 remains active;
the continuous audit does not stop at this checkpoint.
