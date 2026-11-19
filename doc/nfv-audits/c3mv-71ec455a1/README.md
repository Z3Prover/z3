# c3mv relative to master: NFV-methodology audit

**2026-11-19: nine translated properties verified; one conditional MODEL
refutation.** The refutation concerns negative-containment prefix pruning. A
candidate guard proves the complete original property within the selected
model domain. No production source was changed.

These are results about **manually translated Dafny models under disclosed
assumptions**, not confirmed C++ bugs or proofs of source correctness. This was
a local application of the installed NFV workflow's instructions, **not an
execution of its hosted deterministic driver**. Source reachability and native
end-to-end behavior remain unverified.

## Immutable scope

| Input | Revision |
| --- | --- |
| Audited `c3mv` head | `71ec455a18702fe695d0c924a535ff9f385bd58d` |
| Comparison `master` | `d738f81eab9af1468394664a812fe4310ae8e1fa` |
| Merge base | `437536cd64a544a1c329fc57d83e56e294fdf47c` |
| Installed NFV package | `microsoft/neuro-formal-verification@599726579274cfeb1c0915414b911371527a9870` |

The merge-base-to-head delta introduces changes in **104 files**, with 158,837
additions and 323 deletions. Directly comparing the two pinned branch trees
instead gives **107 files**, with 158,838 additions and 397 deletions. These are
different comparisons, not competing measurements of the same diff.

The branch delta includes 89 files under `src`: 30 sequence-facet/engine files,
9 rewriter files, 10 SMT-integration files, 15 other production files, 5 CMake
files and 20 test files. The 129,934-line `c3mv-issue-comparison.md` addition
accounts for much of the overall size and is not production-code coverage.

Since the merge base, pinned master also changed the Pulse repair workflow,
`src/tactic/dependent_expr_state_tactic.h` and `src/test/simplifier.cpp`. In
particular, master's `m_simp->updt_params(m_params)` initialization update is
absent from this head. That is a missing upstream change, **not a regression
introduced by c3mv**, and is not counted as an audit finding.

## Method and evidence boundary

The local [NFV reviewer instructions](https://github.com/z3prover/z3/blob/71ec455a18702fe695d0c924a535ff9f385bd58d/.github/workflows/nfv-pr-review.md)
and source-context instructions pin the upstream package above. Methodology
was taken from that revision's
[workflow guide](https://github.com/microsoft/neuro-formal-verification/blob/599726579274cfeb1c0915414b911371527a9870/workflow/README.md),
[intent-selection prompt](https://github.com/microsoft/neuro-formal-verification/blob/599726579274cfeb1c0915414b911371527a9870/workflow/src/nfv_workflow/intent_prompt.txt),
[translation prompt](https://github.com/microsoft/neuro-formal-verification/blob/599726579274cfeb1c0915414b911371527a9870/workflow/src/nfv_workflow/general_prompt.txt),
[validation rules](https://github.com/microsoft/neuro-formal-verification/blob/599726579274cfeb1c0915414b911371527a9870/workflow/src/nfv_workflow/general_gates.py),
and [follow-up rules](https://github.com/microsoft/neuro-formal-verification/blob/599726579274cfeb1c0915414b911371527a9870/workflow/src/nfv_workflow/followup_prompt.txt).

Ten source-grounded behavioral hypotheses were selected before modeling. They
are inferred properties, not invented quotations of PR intent; no PR was
supplied. Each has one positive whole-property contract, explicit domain
conditions and body-defined helpers. Source was read as immutable text, never
executed, built or imported. No external inference service or hosted workflow
was invoked for the audit.

For each model, checking proceeded through property-free validity, independent
concrete caller/domain checks, and verification of the original whole property.
Only proof annotations changed after the first original-property check;
[freeze checks](nfv-models/freeze.json) preserve computation and contracts.
A failed positive proof was not sufficient for refutation: P1 additionally
required the mechanically negated **complete** property, concrete pins for
every input, and a checked concrete caller. The candidate repair changes only
the entry body and retains all original input/helper contracts and ensures.

[Exact source-tag and metadata checks](nfv-models/provenance.json) passed for
253 source tags. They establish provenance, **not translation equivalence**.
The upstream extractor, full source-span/parser coverage gates, admission,
tool-free sessions and publication driver were not run. These focused,
effect-abstracting slices do not establish acceptance by those full upstream
gates. The outcome counts below describe the **local model checks only**.

## Finding P1: a token-aligned mismatch can hide an interior occurrence

**Conditional MODEL refutation; potential obligation weakening, requiring
source-level investigation.**

The hypothesis is that removing the leading run of determined-mismatch token
positions preserves negative containment. The relevant computation is
[`ncontains_propagation::propagate`, lines 264-301](https://github.com/z3prover/z3/blob/71ec455a18702fe695d0c924a535ff9f385bd58d/src/ast/seq/seq_ncontains_facet.cpp#L264-L301),
using [`compare_alignment`, lines 128-141](https://github.com/z3prover/z3/blob/71ec455a18702fe695d0c924a535ff9f385bd58d/src/ast/seq/seq_ncontains_facet.cpp#L128-L141).
Its source grounding is: "strip the leading run of determined-mismatch
positions."

The selected state has one active obligation and no earlier equation conflict:
haystack tokens `[X, unit(a), Y]`, needle tokens `[X, unit(b)]`. `X` and `Y`
are distinct, non-unit symbolic AST terms. Their interpreted words are kept
separate from those identities; `a` and `b` are distinct constant characters.

| Input | Interpreted value |
| --- | --- |
| `X` | `"aa"`, code points `[97, 97]` |
| `Y` | `"b"`, code points `[98]` |
| `a` | `'a'`, code point `97` |
| `b` | `'b'`, code point `98` |

At token start zero, identical `X` tokens are skipped, then `a != b` gives a
determined mismatch. At token start one, `unit(a)` versus the non-unit `X`
gives unknown. Thus `first_undef_pos` is one and pruning removes all of `X`.
But the original interpreted haystack `"aaab"` contains `"aab"` at **character
offset one**, inside that removed token. The remaining `"ab"` does not.

The model's complete positive property is `before == after`, where these
Booleans observe word containment before and after the transformation. Dafny
proved its negation on all four pinned inputs, with independently checked
domain applicability: [checked input](nfv-models/checks/039-P1-refute.dfy),
[output](nfv-models/checks/039-P1-refute.log) (`5 verified, 0 errors`).
The unsuccessful original proof is [also retained](nfv-models/checks/022-P1-proof.log).
This is a counterexample input and static failure sketch, **not a C++ execution
trace**.

**Applicability limits:** preceding simplifications are assumed not to have
discharged or substituted this obligation. Facet ordering, actual reachability
of this state, later normalization and the solver's final SAT/UNSAT result are
not established. The result does not by itself demonstrate a reachable
source-level soundness bug.

### Model-checked candidate guard

A source-level suggestion is to require every removed token to be a sequence
unit before using token positions as removable character starts:

```cpp
if (has_window && first_undef_pos > 0 &&
    std::all_of(nc.m_haystack.begin(), nc.m_haystack.begin() + first_undef_pos,
                [&](expr* token) { return u.str.is_unit(token); })) {
```

The [candidate model](nfv-models/P1-fixed.dfy) explicitly scans the unit flags
of the same symbolic token shape. It proves the **full original property for
every input in the retained model domain**, not just the counterexample:
[proof](nfv-models/checks/042-P1-fix-proof.log) (`4 verified, 0 errors`),
[validity](nfv-models/checks/049-P1-fix-validity.log), and
[domain including the original witness](nfv-models/checks/050-P1-fix-domain.log).
No input condition or helper contract was weakened.

This is **not a source-verified fix**: the suggested C++ edit was not applied,
compiled or executed. Broader propagation cases, source correspondence and
performance still need review and regressions before adoption. An earlier
quantified candidate guard timed out at 30 seconds; that failed follow-up is
[retained](nfv-models/checks/040-P1-fix-proof.log), not hidden in the final counts.

There were no optional extra assumptions to remove. The original property is
already one short Boolean equality; no useful shorter standalone projection
was identified. No separate simplification proof or global-minimality claim is
made. [Follow-up metadata](nfv-models/followups.json) records these limits.

## All ten selected properties

Each row counts one whole property, including all its conjuncts. Bounds and
abstractions below are essential; full exact preconditions, postconditions,
helper provenance and correspondence limits are in
[properties.json](nfv-models/properties.json).

| ID | Selected behavior and essential scope | Local outcome / checked input |
| --- | --- | --- |
| P1 | Negative-containment prefix pruning, fixed symbolic token shape described above; lengths below `2^31-1`, distinct `a,b` | [Refuted](nfv-models/checks/039-P1-refute.dfy) |
| P2 | Common-prefix and common-suffix cancellation preserve disequality and empty-residual conflict, **resolved character units only**; lengths below `UINT_MAX` | [Verified](nfv-models/checks/023-P2-proof.dfy) |
| P3 | Strict/non-strict lexicographic simplification after common-prefix cancellation, **one resolved-character obligation**, including empty sides | [Verified](nfv-models/checks/024-P3-proof.dfy) |
| P4 | `replace_all` pattern helper: definite match/mismatch soundness and conservative unknown; explicit constant mask, **one-character-width tokens**, bounded index arithmetic | [Verified](nfv-models/checks/037-P4-proof.dfy) |
| P5 | Primitive-root search returns the shortest divisor-period prefix for a nonempty concrete word; not power-trichotomy exhaustiveness | [Verified](nfv-models/checks/026-P5-proof.dfy) |
| P6 | Sorted literal-length scan finds a missing length, including duplicates; successful string branch **after sorting**, no allocation/cancellation model | [Verified](nfv-models/checks/027-P6-proof.dfy) |
| P7 | DFS child-result aggregation: SAT dominates, otherwise cutoff then unknown, UNSAT only for all-UNSAT children; purity requires every child pure and eligible parent | [Verified](nfv-models/checks/028-P7-proof.dfy) |
| P8 | Pending-hypothesis early acceptance requires coherence and no remaining unsupported/higher-order obligation; false hypotheses reset and **fall through**, not necessarily return CONTINUE | [Verified](nfv-models/checks/029-P8-proof.dfy) |
| P9 | All six comparisons with **negative integral decimal thresholds**, assuming valid conversion nonnegative and invalid conversion exactly `-1` | [Verified](nfv-models/checks/030-P9-proof.dfy) |
| P10 | Plus-repetition flattening preserves possible counts of `R` factors, including zero/unit outer cases; **factor-count algebra**, not source regex-AST equivalence | [Verified](nfv-models/checks/038-P10-proof.dfy) |

P2/P3 do not establish symbolic-word-token behavior. P4 does not model arbitrary
variable-length tokens. P7 treats child verdicts as explicit inputs to check
their aggregation, not as assumed proof of recursive solver correctness; scope
undo, dependency joins and cache insertion are excluded. P8's explicit
fall-through observation stops at the selected branch boundary: it is not a
proof of all `final_check_eh` paths. P9 does not prove a decimal parser or
nonnegative-threshold language construction. P10 counts derivation factors,
not characters, so an `R` accepting epsilon is not silently treated as having
positive word length.

## Toolchain, diagnostics and reproduction

Dafny reported `4.11.0+fcb2042d6d043a2634f0854338c08feeaaaf4ae2`;
its explicitly selected bundled solver reported `Z3 version 4.12.1 - 64 bit`.
The official
[Windows archive](https://github.com/dafny-lang/dafny/releases/download/v4.11.0/dafny-4.11.0-x64-windows-2022.zip)
SHA-256 was checked against the GitHub release asset digest:
`3653f05a111ca21e234709ea7b25ce96083fd6c6f10484256ba54110dbc0654d`.
Do not substitute the archive's other bundled solver, Z3 4.14.1.

Checks used two cores and a 30-second limit **per assertion batch**, not a
whole-audit time limit. Quantifier-trigger warnings remain visible.
`--allow-warnings` allows those warnings, not failed obligations. P1's refutation,
P4/P10's proofs and related checks additionally used
`--solver-option O:smt.mbqi=true`: sound model-based quantifier instantiation
without changing computation/contracts or disabling obligations. This is an
explicit local configuration difference from the hosted default.

[checks.json](nfv-models/checks.json) retains **50 verification attempts**:
exact checked Dafny inputs, commands, exit codes, hashes and durations, with
full outputs under `nfv-models/checks`. Failed attempts and the follow-up
timeout remain present. Their measured verifier-subprocess durations total
119.610 seconds; this is not total audit elapsed time. Early syntax-resolution
diagnostics are included separately; complete inputs are retained for the 50
verification attempts, not every earlier syntax draft.

Only local-machine path prefixes in published command/log text were replaced
with portable `$DAFNY`, `$Z3` and relative audit paths. Checked `.dfy` bytes and
their SHA-256 values were not changed. [manifest.json](manifest.json) hashes the
published artifacts. No downloaded verifier binaries or source changes are
included. Directory-local Git attributes preserve LF line endings so checkout
conversion does not invalidate the recorded byte hashes.

From the repository root in PowerShell, after extracting the checked official
archive, set `$dafny` and `$z3` to its `Dafny.exe` and `z3\bin\z3-4.12.1.exe`:

```powershell
$audit = Resolve-Path 'doc\nfv-audits\c3mv-71ec455a1'
python "$audit\check_nfv_provenance.py"
& $dafny verify "$audit\nfv-models\checks\039-P1-refute.dfy" --solver-path $z3 --verification-time-limit 30 --cores 2 --allow-warnings --solver-option 'O:smt.mbqi=true'
& $dafny verify "$audit\nfv-models\checks\042-P1-fix-proof.dfy" --solver-path $z3 --verification-time-limit 30 --cores 2 --allow-warnings --solver-option 'O:smt.mbqi=true'
```

The checked inputs already contain their domain drivers where appropriate.
Both commands above should succeed. Verifying canonical `P1.dfy` positively
is **not** expected to succeed. The optional [runner](run_nfv_audit.py) can
regenerate validity/domain/whole-property/refutation checks using the metadata;
it appends new evidence, so use a separate copy of this audit directory for new
runs. For example, `--phase proof --select P4 P10 --mbqi`, together with
`--dafny` and `--solver`, reproduces those positive checks. Runner failures
return nonzero rather than treating a failed proof as success.

## Coverage and remaining uncertainty

This was risk-directed inspection and ten focused translations, **not an
exhaustive audit of all 104 files**. Source ranges/diffs were examined across
the equality, lexicographic, negative-containment, replacement, power,
membership, higher-order, conversion and regex-equality facets; nseq final
checks and arithmetic integration; the search tree; decimal/regular
preprocessing; predicate algebra; ground sequence/repetition rewriting; and
selected derivative/witness and tactic integration changes. Headers, build
registrations and tests were also inventoried or sampled, not universally
verified. Tests were intention evidence, not executed tests.

Unproved areas include full automata/derivative equivalence, all regular
preimages, trichotomy completeness, quantifier witnesses, cache/core soundness,
AST lifetimes, aliasing, egraph/trailing/backtracking correctness, complete
model reconstruction, native solver integration and performance. F* additions
and generated issue inventories were outside this Dafny audit. Numeric bounds
and mathematical-integer abstractions are disclosed per model; no general
machine-semantics correspondence is claimed.

The work ran in five scheduled stages: pinned-methodology/toolchain discovery,
change mapping/property selection, model construction, checking/follow-ups,
and report publication. A recurring 10-second schedule separated stage turns;
verification was not run concurrently against the same artifacts. No native
build or unit suite was run, consistently with the NFV rule that inspected
source is data, not executable audit input.
