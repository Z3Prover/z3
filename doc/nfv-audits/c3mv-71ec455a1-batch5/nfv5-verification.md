# Batch 5 verification: valid translations, unresolved whole properties

Status: verification complete; publication is the next separate scheduled stage. This is a manual local NFV-methodology audit, not an official hosted-driver report or a C++ equivalence proof.

## Result

All three property-free model-validity checks pass. Only P22 admits its complete original concrete-domain group (four examples). No complete original property is verified or refuted. All three whole-property outcomes are **resources exhausted**, with different gate positions:

| Whole intent | Independent domains | Entire original property | Outcome |
| --- | --- | --- | --- |
| P20, `power_facet::apply_subst` | Four examples not admitted | Blocked by domain gate | Resources exhausted at admission |
| P21, `cache_insert` | Five examples not admitted | Blocked by domain gate | Resources exhausted at admission |
| P22, `constraint_store::intern` | All four admitted | Ordinary proof fails; isolated MBQI proof times out | Resources exhausted after admission |

There are 16 verifier attempts: four successful checks and 12 unsuccessful checks, including 11 attempts with per-obligation timeouts, a wall timeout, or external resource interruption. The four successful checks are three validity checks and one four-example domain group, **not four verified properties**. Internal obligations (for example 470, 469 or 88 verified batches) are not whole properties or independently admitted examples. Seven prior construction/provenance/resolution checks passed. There were zero native executions, accepted counterexamples, shorter-property refutations or repair proofs.

## Scope and unchanged intent

Source is pinned to `71ec455a18702fe695d0c924a535ff9f385bd58d`; master is `c2460a558fc6fee3cf15cfebd2d3f642ebf77770`, with merge base `437536cd64a544a1c329fc57d83e56e294fdf47c`. NFV methodology is pinned to microsoft/neuro-formal-verification at `599726579274cfeb1c0915414b911371527a9870`. Older batches using a different master are not silently rebaselined.

This is the same-intent retranslation of batch 4, not three new source entries. The pre-frozen plan changes exactly five helper-body lines: three `Widths` lambda accesses use existing total accessor `R`; P20 `Deactivate` uses existing `B`; P20 `Rebase` uses `R` for its row accesses. The entire entry methods, all 45 inputs, 19 outputs, 14 mandatory requires, nine original ensures (three per whole intent), helper signatures/contracts/metadata and all 13 example assignments remain unchanged. No optional restrictions were introduced or removed. The new models remain byte-identical to their batch-5 seal throughout verification. Batch-4 failures remain intact and are not overwritten or relabeled.

See [modeling](nfv5-modeling.md), [plan](nfv5-retranslation-plan.json), [exact diff](nfv5-retranslation-diff.json), [seal](nfv5-model-freeze.json), and [complete contracts and examples](nfv5-models/properties.json). Source tags establish provenance, not translation equivalence. Helpers have bodies; no assumptions, bodyless oracles, weakened goals or new helper contracts were used to force acceptance.

## Findings and proof boundaries

**P20** retains the full remove/register/rebase update, exact representation/metadata effects, and the source-inferred implication preserving a cycle-free active mutable-base graph. The immutable syntax catalog is distinct from mutable current bases. Checked harness hints expose concrete partitions and prove a catalog-cycle argument; they do not assert caller reachability. Remaining failures include concrete `Rows` unfolding assertions and the unsigned-width/substitution-size precondition. None supplies an accepted independently checked domain group. Apparent progress on later assertions can depend on earlier unproved assertions and is not independent evidence. The conditional gpower producer/rebase candidate, later self-binding/elimination, and native reachability remain unresolved.

**P21** retains complete eligibility, collection, dependency filtering, interning and watch updates. The semantic goal concerns contradiction under fixed background, separately from a temporary length guess. The candidate languages `{a,bb}` and `{b,bb}` share `bb` while sharing no word at guessed length one. This remains a conditional source/model investigation, not a witnessed native cache bug. Both isolated strategies failed to complete domain admission within bounded resources. The actual native conflict/core, insertion and later cache-hit chain remains unproved.

**P22** admits four complete independently checked callers. Its full original conjunction includes canonical structural ownership/IDs, exact hit-or-clone transition and canonical-class preservation. The ordinary positive has four postcondition diagnostics, including search-completeness/bounds and sequence-state/class obligations. These are unresolved proof obligations, not a counterexample. The final isolated MBQI attempt reports 88 internal obligations verified and four timeouts at the complete original postconditions. No helper contract was strengthened after freeze. A future sound proof may require checked search-completeness and sequence-update lemmas without changing helpers or goals.

## Exact attempt ledger

All checked inputs, full logs, command lines, versions/options and raw hashes are retained in [checks.json](nfv5-models/checks.json) and its `checks` directory. Every attempt retains the full relevant model; no symbol filters or skipped verification dependencies were used.

| Attempt | Intent | Phase | Seconds | Exit |
| --- | --- | --- | --- | --- |
| 1 | P20 | validity | 2.230 | 0 |
| 2 | P21 | validity | 2.445 | 0 |
| 3 | P22 | validity | 1.825 | 0 |
| 4 | P20 | domain | 37.324 | 4 |
| 5 | P21 | domain | 93.825 | 4 |
| 6 | P22 | domain | 1.986 | 0 |
| 7 | P20 | MBQI domain | 58.676 | 4 |
| 8 | P21 | MBQI domain | 93.746 | 4 |
| 9 | P22 | complete original positive | 2.030 | 4 |
| 10 | P20 | checked unfolding, MBQI domain | 63.594 | 4 |
| 11 | P21 | checked unfolding, MBQI domain | 95.545 | 4 |
| 12 | P20 | isolated checked unfolding, MBQI domain | 190.180 | 4 |
| 13 | P21 | isolated checked unfolding, MBQI domain | 1887.870 | 4294967295, externally interrupted |
| 14 | P20 | final isolated checked unfolding, default domain | 81.567 | 4 |
| 15 | P21 | final isolated checked unfolding, default domain | 604.769 | 124, harness wall timeout |
| 16 | P22 | isolated MBQI complete original positive | 66.145 | 4 |

The trusted toolchain is Dafny `4.11.0+fcb2042d6d043a2634f0854338c08feeaaaf4ae2` and explicitly selected bundled Z3 `4.12.1`, not checkout Z3 or the other bundled version. Base flags are `verify INPUT --solver-path SOLVER --verification-time-limit 30 --cores 2 --allow-warnings --show-snippets false`. Sound supplemental MBQI is `--solver-option O:smt.mbqi=true`; isolation is `--isolate-assertions`. Attempts 14-16 additionally stream `--progress Symbol`. This is logging, not a proof restriction. The runner permits only one history writer; no verifiers ran in parallel.

Harness annotations assert concrete suffix/partition/finite-language facts and a checked P20 catalog-cycle argument; they add no entry/helper preconditions or assumptions. Warnings about missing triggers and P21 indentation remain in the unabridged logs. Failed checked annotations are not promoted to facts in the report.

## Resource-control intervention

The per-obligation 30-second option did not bound total isolated runtime. Attempt 13 retained two owned solver children; one consumed 1611.6875 CPU seconds. A 30-minute wall ceiling was recorded before it expired. At `2026-11-19T13:50:43.0334278-05:00`, only the confirmed owned long-running solver PID 78856 was stopped. After a further grace interval, the still-running exact owned verifier PID 72756 and its then-child 89184 were stopped at `13:52:09.8110689-05:00`. Ownership was rechecked using exact input/session command line and parent IDs. The runner retained its warning output and the actual process exit `4294967295`. This is **external resource interruption**, not an unintervened Dafny result, native solver crash, accepted domain or refutation. See the [separate intervention receipt](nfv5-attempt13-resource-intervention.json).

For subsequent attempts the trusted harness streams partial output and enforces a 600-second wall watchdog in addition to the per-obligation limit. On expiry it stops only that attempt's descendant process tree with explicit process IDs, retains the partial log, adds a clearly marked harness diagnostic, records actual interrupted-process exit separately, and assigns harness status 124. Attempt 15 exercised this limit. No historical input/log/history bytes were rewritten to add these fields. The retained [watchdog tests](test_nfv5_watchdog.py) pass three cases: live success, unchanged nonzero exit without cleanup, and live owned parent/child timeout cleanup with child absence checked. These tests run trusted Python subprocesses only.

## Independent evidence validation and preservation

[The finalizer](finish_nfv5_verification.py) validates every frozen/baseline hash, draft history, every checked input/log hash, complete original entry contracts, exact property-free validity removal, every original typed example assignment and caller, complete positive-file equality, gate order, explicit pinned solver/core/time settings, isolation recording and the separate interruption receipt. It refuses to finalize with unrecorded active inputs/logs or unsupported refutation/repair records. [Machine results](nfv5-results.json) record zero accepted proofs/refutations and three resources-exhausted whole intents.

At handoff, branch remains `c3mv`, HEAD remains `f975e94d9830bcca332b309df422b364c6e99191`, source tree remains `caa5a9922f074f9f4adc8f7c98e1685be9626503`, stash ref remains `7af7fad70e9cea38601c67ff00d89f6b5576c2d6`, and the repository worktree is clean. All four prior publications are unchanged. No production source was executed, built, imported or patched.

## Next stage and continuing work

Publish this bounded checkpoint in a distinct batch-5 directory, preserving full historical raw bytes and line-ending exceptions. Portable replay must retain isolation and resource-control metadata; do not automatically rerun expensive interrupted checks. Validate report links, manifests, provenance, tooling, indexed/committed bytes and remote publication. Then continue the scheduled audit with genuine remaining coverage/source-applicability/proof work; do not stop schedule 2. [Followups](nfv5-followups.json) separate unresolved native applicability from proof-engineering gaps. This batch makes no new native bug claim.
