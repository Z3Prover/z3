# c3mv NFV audit: batch 5 translation and proof checkpoint

**No new confirmed bug, whole-property proof or refutation.** All three revised models pass property-free validity; P22 admits four concrete examples. P20/P21 remain resource-exhausted at domain admission, and P22 remains resource-exhausted at its complete original property. This is a local audit using pinned NFV/Dafny methodology, not an official hosted-driver report or source equivalence proof.

| Whole intent | Validity | All original concrete domains | Whole-property outcome |
| --- | --- | --- | --- |
| P20 `power_facet::apply_subst` | Pass | Not admitted | Resources exhausted before positive check |
| P21 `cache_insert` | Pass | Not admitted | Resources exhausted before positive check |
| P22 `constraint_store::intern` | Pass | Four admitted | Original proof unresolved; final strategy times out |

Read the [full verification report](nfv5-verification.md), [machine results](nfv5-results.json), [modeling report](nfv5-modeling.md), [complete property/helper/domain metadata](nfv5-models/properties.json), and [all 16 exact verifier attempts](nfv5-models/checks.json). The three properties are the same batch-4 intents, **zero new source coverage**. Exactly five preplanned helper-body lines were retranslated; complete entry methods/contracts/goals/examples remain unchanged. See [frozen plan](nfv5-retranslation-plan.json), [exact diff](nfv5-retranslation-diff.json) and [model seal](nfv5-model-freeze.json).

Source `71ec455a18702fe695d0c924a535ff9f385bd58d`, master `c2460a558fc6fee3cf15cfebd2d3f642ebf77770`, merge base `437536cd64a544a1c329fc57d83e56e294fdf47c`; NFV upstream microsoft/neuro-formal-verification at `599726579274cfeb1c0915414b911371527a9870`. Remote master advanced after verification to `bcad05a7bf7dd9b82bd7a665018e0480e737264b`; that revision was not silently substituted into this batch. The [preflight](publication-preflight.json) preserves the distinction and independently checks pinned source blobs/excerpts. Source remains immutable text: no production execution, builds, imports or patches.

There are 16 audit attempts: four successful gate checks, twelve unsuccessful checks, including eleven timeout/interrupted attempts. Attempt 13 was externally interrupted at a recorded 30-minute wall ceiling plus grace, not a native solver crash; its [separate receipt](nfv5-attempt13-resource-intervention.json) preserves exact ownership checks and process exits. Attempt 15 hit a new 600-second harness watchdog. Internal verified obligations are not whole properties. All three failed whole intents remain open; see [followups](nfv5-followups.json).

## Reproduce validation

On Windows with Python 3, from this directory:

```powershell
python -B .\validate_nfv5_publication.py
python -B .\test_nfv5_replay.py -v
python -B .\test_nfv5_watchdog.py -v
python -B .\replay_nfv5_checks.py --dafny C:\trusted\dafny\Dafny.exe --solver C:\trusted\dafny\z3\bin\z3-4.12.1.exe --output C:\temp\nfv5-replay-new
```

Use official Dafny 4.11.0 with explicitly selected bundled Z3 4.12.1, not checkout Z3 or the other bundled version. The official archive SHA-256 is `3653f05a111ca21e234709ea7b25ce96083fd6c6f10484256ba54110dbc0654d`. Installation provenance and the pinned method are in [methodology](nfv-methodology.md); its old initial schedule-stop paragraph is superseded by the user's continuous-operation instruction.

Replay defaults to successful gate attempts 1, 2, 3 and 6, running serially with two cores, a 30-second per-obligation limit and a 600-second wall watchdog. It verifies input hashes before execution, requires output outside this immutable bundle, and retains MBQI/isolation/progress settings. Other attempts require explicit `--select`; interrupted checks additionally require `--allow-resource-checks`. A manual historical interruption cannot be deterministically reproduced as the same raw process exit. Never treat a failed replay or later matching result as masking an earlier mismatch. Tool tests use trusted Python subprocesses or mocked outcomes, not production source.

The [tool-validation receipt](tool-validation/results.json) records four live gate replays and seven focused tooling tests, separately from audit evidence. Historical construction/verification scripts are archived for provenance and may contain original session paths; use the portable validator/replay tools above for the exported bundle.

## Integrity and continuation

[Manifest](manifest.json), [export notes](export-notes.json), [verification handoff](nfv5-verification-handoff.json) and [original sealed selection](nfv5-original-selection.json) preserve full lineage, raw hashes, complete goals/domains and line-ending exceptions. Historical CRLF bytes are not normalized. Every recorded failed input/log and warning remains available. All four prior audit reports, source tree and user stash remain unchanged.

Continuous schedule 2 stays active after publication. The next batch reconciles the newly observed master revision and continues genuine unresolved source-applicability/proof/coverage work; this checkpoint is not completion of the continuous audit.
