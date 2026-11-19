# c3mv NFV/Dafny audit: batch 4

**Three translation-validity failures; no new verified property or refutation.**
Source investigation identified conditional power-substitution and cached-core
sufficiency hypotheses, but the frozen models failed the property-free gate.
Those hypotheses are NOT confirmed native bugs, solver errors or crashes.

This is a manual local audit following the pinned NFV/Dafny methodology, not
an official hosted-driver report or C++/Dafny correspondence proof. Production
source was read as immutable text only: no build, execution, import or patch.

## Immutable scope

| Input | Revision |
| --- | --- |
| Audited source | `71ec455a18702fe695d0c924a535ff9f385bd58d` |
| Master comparison | `c2460a558fc6fee3cf15cfebd2d3f642ebf77770` |
| Merge base | `437536cd64a544a1c329fc57d83e56e294fdf47c` |
| NFV methodology | `microsoft/neuro-formal-verification@599726579274cfeb1c0915414b911371527a9870` |
| Previous publication | `13cfdf0d3f046886dd16ae6aef2c9853679b4877` |

The source and master pins match batch 3. Earlier batches keep their earlier
master baseline; none of their evidence or verdicts is rewritten. This batch
is focused coverage, not an exhaustive correctness audit of the branch.

## Source investigation: hypotheses and limitations

The [producer ledger](nfv4-subst-producer-ledger.json) classifies all 24 known
substitution broadcasts in 16 scopes, with exactly three concrete chain
attempts. Active-equation rewriting blocks the simple reverse-binding attempt;
a unit-base guard blocks the variable-decomposition attempt. The remaining
conditional gpower chain registers `Q=power(X,k)` before broadcasting `X->[Q]`.
Rebasing can then make Q's separately stored CURRENT base contain Q itself.
The immutable AST remains a DAG; that does not establish a DAG of current
bases. See the [complete trace](nfv4-subst-invariants.md), including exact
guards, dependency handling, cached freshness and competing-splitter limits.

If later k=1 unfolding emits a self-binding and elimination is reached, that
would create a termination concern. Full native producer/driver reachability,
prior propagation, splitter priority, backtracking and the later call are NOT
established together. No native hang or crash was attempted or observed.

The [conflict/core investigation](nfv4-core-provenance.md) captures sixteen
additional files and classifies 28 textual direct facet-conflict sites:
27 active and one disabled. Null dependencies are empty/unconditional, not
automatically missing proof. Cache state is cleared on EVERY solve entry;
reuse is within branches/depth rounds of one solve, not across solve calls.
Excluded-facet eligibility is satisfaction, not emptiness.

The source-level sufficiency candidate uses languages `{"a","bb"}` and
`{"b","bb"}`. They share `"bb"`, but not a word of guessed length1. Witness
extraction can use a temporary exact-length premise absent from the cached
signature. A correct conditional conflict need not make the membership-only
signature contradictory. Actual earlier processing, model choice, helper core,
insertion and later hit remain unproved. The prior P19 pointer-alias mismatch
may suppress such hits. An insufficient stored signature is NOT itself an
observed wrong UNSAT result. [Full dependency ledger](nfv4-core-provenance-ledger.json).

## Whole-property selection and verification

The [selection](nfv4-selection.json) froze three distinct changed entries
before modeling, including a positive comparison rather than only suspected
failures. Each property retains ALL THREE original positive conjuncts.

| Entry | Entire selected intent | Gate outcome |
| --- | --- | --- |
| P20 `power_facet::apply_subst` | Structural state, exact remove/register/rebase update, acyclic mutable-base preservation implication | Translation/audit failure |
| P21 `cache_insert` | Structural storage/watch state, exact insertion update, semantic contradiction preservation under fixed background | Translation/audit failure |
| P22 `constraint_store::intern` | Canonical structural ownership/IDs, exact hit-or-clone update, canonical-class preservation | Translation/audit failure |

There are 62 body-defined helpers, 14 mandatory requires clauses, no optional
restrictions, and thirteen fully specified example inputs. Successful resolution
of the three models and typed domain drivers did NOT establish well-definedness
or domain admission. Twenty construction checks are retained, including all
three initial domain-resolution failures and their corrected typed drivers.

Exactly three audit verifier attempts ran. [001 P20](nfv4-models/checks/001-P20-validity.dfy),
[002 P21](nfv4-models/checks/002-P21-validity.dfy), and
[003 P22](nfv4-models/checks/003-P22-validity.dfy) remove ONLY the entry ensures.
Every requires, helper contract and computation remains intact. Each failed
with exit4: `Widths` indexes an unguarded sequence-constructor lambda parameter;
P20 additionally has the same issue in `Deactivate` and two `Rebase` accesses.
For P22 the invalid shared helper is unused by interning itself. These are
translation failures, not native out-of-range accesses. See the
[complete interpretation](nfv4-verification.md), [results](nfv4-results.json),
and [exact command/input/log ledger](nfv4-models/checks.json).

The failed gate prevented all domain, original-positive, refutation, shorter-
consequence and candidate-repair checks. No failed positive proof was called a
refutation; no witness was admitted or native finding established. P21's warning
is preserved. There were no timeouts or MBQI retries. The frozen model policy
permits only sound assert/invariant/decreases annotations, not fixing helper
computation/contracts in place. All failures and frozen files stay unchanged.

## Evidence, assumptions and replay

[Model metadata](nfv4-models/properties.json) records every input, requires,
helper, source anchor, full original goal, example and correspondence limit.
Finite-language semantics, mathematical rows/tuples, successful allocation and
canonical membership ADTs remain abstractions. Mutable-graph acyclicity is not
an assumed input invariant. Unknown closing verdicts are not admitted oracles.
Totalizing some access helpers did not make every lambda access well-defined.
Source tags validate cited text, not full upstream extraction/admission or
translation equivalence. All original local checks and source-tool capture
failures remain disclosed in their exact historical records.

[Selection seal](nfv4-selection-freeze.json), [model seal](nfv4-model-freeze.json),
[verification handoff](nfv4-verification-handoff.json), exact pinned-source
inventories, every checked input/log and tool source are included. Historical
author/check/finalize tools retain session assumptions and are not the portable
interface. Portable validation and replay are provided below. Historical
handoffs retain their original paths and stage-next markers; THIS README is
the publication entry point. [Export notes](export-notes.json) explain raw
CRLF exceptions to the normal LF policy; [manifest](manifest.json) binds bytes.

Use official Dafny4.11.0 and explicitly choose bundled Z3 4.12.1, not4.14.1.
Every attempt used two cores, a30-second per-obligation limit and retained
warnings. Replay checks EXPECTED exit codes: reproducing an expected failure
is not a successful mathematical proof. It writes outside the immutable bundle.

```powershell
python .\validate_nfv4_publication.py
python .\replay_nfv4_checks.py --dafny C:\trusted\dafny\Dafny.exe --solver C:\trusted\dafny\z3\bin\z3-4.12.1.exe --output C:\audit-replay\batch4
```

Three separately labeled LIVE replay invocations validate reproducibility;
mocked tool tests check that a later match cannot mask an earlier mismatch
and that changed input bytes are rejected. [Tool validation](tool-validation/results.json)
is NOT counted as new audit attempts or source findings.
The first replay test launch targeted an output directory inside the bundle;
the isolation guard rejected it BEFORE any verifier ran. Exact original tools
and diagnostics are retained in `tool-validation/attempts`. The corrected live
replay writes externally, then its completed logs are copied into this bundle.

## Continuous follow-up

Publication is a checkpoint, not completion. [Follow-ups](nfv4-followups.json)
require a NEW explicitly identified translation revision for the SAME three
whole-entry intents, without new source-property coverage credit. Correct
lambda definedness while preserving intended evaluated-index values, all input
contracts, entire goals and thirteen examples; freeze the revision before its
own validity/domain/proof checks. Preserve this failed evidence. P13/P18 and
the native reachability questions remain open. The requested10-second stage
schedule stays active.
