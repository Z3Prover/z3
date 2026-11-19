# c3mv correctness audit, batch 2: local NFV/Dafny evidence

**Four whole translated properties verified, two conditionally refuted, and one
proof unresolved.** Neither refutation is a confirmed native solver bug or crash.
This continues the [first audit](../c3mv-71ec455a1/README.md), using the pinned
[NFV methodology](nfv-methodology.md) manually and locally, not the hosted NFV
driver. Production source was read as immutable text, never built or executed.

| Immutable input | Revision |
| --- | --- |
| Audited c3mv source | `71ec455a18702fe695d0c924a535ff9f385bd58d` |
| Comparison master | `d738f81eab9af1468394664a812fe4310ae8e1fa` |
| Merge base | `437536cd64a544a1c329fc57d83e56e294fdf47c` |
| NFV methodology | `microsoft/neuro-formal-verification@599726579274cfeb1c0915414b911371527a9870` |
| Prior report commit | `69b9548ea0b4fad73762f95d5633b21571706d70` |

The branch-introduced comparison and direct master tree comparison are distinct;
see the [coverage ledger](nfv2-coverage-ledger.json). It classifies all 89 changed
`src` files: 64 production, 20 tests, five build files. Models cover focused
properties, not complete functions or all changed files. Seven intents were
[selected and frozen](nfv2-selection.json) before implementation; no ten-property
quota or security assessment was used. Scope is logical correctness and crashes.

## Findings and proof gap

### F1 extension: token-alignment full discharge can miss an internal occurrence

`ncontains_propagation::propagate`, lines 264-291, uses token windows to discharge
a negative containment when all windows mismatch. Model P11 examines haystack
`[X,unit(a),Y]`, needle `[X,unit(b),Z]`, with distinct opaque X/Y/Z identities
and distinct resolved unit characters a/b. The sole token window matches X and
then mismatches a/b, causing full discharge.

The every-input witness is X=`aa`, Y=`b`, Z=empty, a=`a`, b=`b`. Interpreted
haystack `aaab` contains needle `aab` at **character offset one**, despite the
token-window mismatch. The [complete negation and concrete caller](nfv2-models/checks/030-P11-annotation-refute.dfy)
[verify](nfv2-models/checks/030-P11-annotation-refute.log). Removing both optional
word-length restrictions retains the [refutation](nfv2-models/checks/035-P11-optional-removed-refute.log).
A strictly shorter consequence is proved with all inputs/output free, then
separately refuted; this is bounded reduction, not a minimality claim.

**This is the same token-versus-character root-cause concern as first-batch P1,
extended to a different branch, not another confirmed native bug.** The previous
candidate guarded prefix pruning only; it did not repair full discharge. The
[source-applicability follow-up](nfv2-p1-source-trace.md) traces normalization,
facet order, substitution, deactivation and later processing. Earlier word
equalities can replace opaque variables before this branch, so directly asserting
X=`aa` or Z=empty does not establish a native reproduction. Native reachability
and an end-to-end wrong SAT/UNSAT result remain unproved.

### F2: unsigned replacement-case threshold refutes mathematical admission

`replace_all_split::apply_case`, lines 215-229, evaluates
`c >= 2 * p.length() + 2` with unsigned arithmetic. P12 explicitly models both
32-bit wrapping operations. At pattern length **2,147,483,647**, case **1**, the
mathematical threshold is 4,294,967,296 but the source-width threshold is zero:
the guard rejects case 1. This refutes the source-inferred hypothesis that
admission equals `case_number < 2 * pattern_length + 2` in mathematical integers.
The independent domain and [entire-property negation/caller](nfv2-models/checks/022-P12-refute.dfy)
[verify](nfv2-models/checks/022-P12-refute.log). A shorter false-rejection
consequence is independently implied with free inputs/output and refuted.

**Large-literal reachability is unproved.** The witness is scalar; no giant
literal was constructed or allocated. Buffer/caller limits, actual allocation,
native crashes and solver-result consequences are not established. The
[candidate model](nfv2-models/P12-candidate.dfy) changes only the entry threshold
to nonwrapping mathematical arithmetic; unchanged helper/input contracts and
the **entire original postcondition** [verify generally](nfv2-models/checks/042-P12-candidate-proof.log).
This is an admission-prelude experiment, not a complete replacement/case-iterator
repair, a production patch, or an end-to-end native fix.

### P13: queue relation remains unresolved, not refuted

Validity and independent concrete domains pass. The original complete property
still has [unproved conflict/queue relational obligations](nfv2-models/checks/031-P13-proof.log).
No counterexample was established. The NFV category is **audit/proof-check
failure**, not a syntax/type error, timeout, or source bug. Unproved relational
loop invariants were removed as proof annotations, never from the complete goal.
Bounds-only reasoning is not substituted or counted as a successful property.

## All selected whole properties

| ID | Focus and result | Primary evidence |
| --- | --- | --- |
| P11 | Negative-containment full-discharge preservation: **model refuted** | [checked input](nfv2-models/checks/030-P11-annotation-refute.dfy) |
| P12 | Unsigned replacement-case admission equals mathematical range: **model refuted** | [checked input](nfv2-models/checks/022-P12-refute.dfy) |
| P13 | Request conflict, stable retained queue, head update and bounds together: **unresolved** | [checked input](nfv2-models/checks/031-P13-proof.dfy) |
| P14 | Selected `str.at` preimage membership equivalence: **model verified** | [checked input](nfv2-models/checks/018-P14-proof.dfy) |
| P15 | First replacement preserves a character absent from needle/replacement: **model verified** | [checked input](nfv2-models/checks/019-P15-proof.dfy) |
| P16 | Erase-trail restoration equals original sequence, with modeled access domains: **model verified** | [checked input](nfv2-models/checks/032-P16-proof.dfy) |
| P17 | Complete tri-valued conjunction/disjunction fold: **model verified** | [checked input](nfv2-models/checks/020-P17-proof.dfy) |

The [result ledger](nfv2-results.json), [full verification handoff](nfv2-verification.md),
[modeling handoff](nfv2-modeling.md), [property/helper metadata](nfv2-models/properties.json),
and [frozen baseline](nfv2-model-freeze.json) disclose exact domains, assumptions,
helpers, hashes, proof changes, and correspondence limits. All helpers have
bodies; no assumes, axioms, bodyless helpers, verifier attributes or suppressed
obligations were used. Computation/contracts remained frozen; only sound proof
annotations changed. Provenance checks validate 171 exact source tags across
nine pinned files, **not translation equivalence**. Full upstream extraction,
parser, span-coverage and admission gates were not run.

P14 covers only the selected epsilon/singleton observation and index domain;
its extra word-length bound is disclosed. P15 models helper loops by decreasing
pure recursion, including empty needle/no match/first-only replacement, with
the matching contract and erased proof lemma verified from bodies. P16 models
integer records and actual left erase/backwards restoration, not native object
lifetimes, allocation, moves or aliasing. P17 abstracts child verdicts and does
not verify recursive regex truth, budgets or native AST arities. These proofs
do not establish whole-solver correctness or native memory safety.

## Reproduction and evidence integrity

Dafny **4.11.0** and explicitly selected Z3 **4.12.1** were used, at two cores
and 30 seconds per assertion batch. The official archive digest and exact
versions are recorded in the methodology. No binaries are committed.
[All 42 audit verification attempts](nfv2-models/checks.json) retain byte-exact
inputs, logs and commands: **32 succeeded, ten did not**, including one MBQI
timeout. P11's accepted refutation uses default solving, not that timed-out run.
Quantifier-trigger warnings remain visible. The 16 earlier provenance/resolve
draft checks are separate. Publication-tool smoke tests are also separate from
these 42 audit attempts; see [tool validation](tool-validation/results.json).

Checked inputs/logs retain original bytes and local paths. Historical handoffs
retain their original paths, with LF-only normalization recorded below.
The separately authored portable tools below do not require
those paths. Run from this directory in a checkout containing the pinned Git
objects, with trusted verifier paths; output must be outside this report:

```powershell
python validate_publication.py
python check_nfv_provenance.py
python replay_checks.py --dafny C:\tools\dafny\Dafny.exe --solver C:\tools\dafny\z3\bin\z3-4.12.1.exe --select 022 031 --output C:\audit-replay
```

Replay checks raw input hashes before invoking the supplied trusted Dafny, never
executes commands from recorded metadata, retains new logs separately, and
compares exits with recorded outcomes (031 is an expected proof failure).
Omit `--select` to replay all 42, including failures and the resource-sensitive
timeout; differences must be investigated, not relabeled as original results.
[The runner](run_nfv_audit.py) also supports `--models`, phase/selection and an
entry-only variant; failed selected checks return nonzero even if a later check
succeeds. Run new experiments on a separate model-directory copy, not this
immutable published evidence set.

[Historical authoring tools](historical-tools/make_nfv2_models.py) retain their
original content/workspace assumptions, with document/script CRLF endings only
normalized to LF as [recorded](export-notes.json); do
not rerun the generator over the final proof-annotated models. The standalone
runner/checker differ from batch 1 only in their default model-directory name.
[The manifest](manifest.json) hashes every published file except itself. Local
Git attributes preserve LF bytes; raw indexed Git blobs were checked before
commit. Original first-batch evidence is untouched. Continuous scheduled auditing
continues after publication; remaining coverage and the queue proof gap are not
silently treated as completed.
