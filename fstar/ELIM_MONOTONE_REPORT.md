# Monotone real-variable elimination: NFV soundness audit

## Result

The main property of `elim_monotone` is **equisatisfiability with
model reconstruction**, not pointwise equivalence.

Let `F` be the original assertions, `G` the reduced assertions, `E` the
eliminated real constants, and `R` the recorded model converter.
The required contract is:

```text
well_sorted(F)                         => well_sorted(G)
well_formed(M) and M |= F               => M |= G
well_formed(M) and M |= G               => well_formed(R(M)) and R(M) |= F
y not in E                             => R(M)(y) = M(y)

Consequently: SAT(F) iff SAT(G), and UNSAT(F) iff UNSAT(G).
```

**Yes, the reconstruction preserves well-formed models:** it changes only
uninterpreted real constants and assigns them real-valued witnesses. It
also produces a model of the original assertions from any model of the
reduced assertions. This is stronger than merely proving that the result
has the right types.

**No, a reduced model is not necessarily an original model unchanged.**
For example, `x > 0` reduces to `true`. The well-formed assignment `x = 0`
models the reduced formula but not the original one. Reconstruction
assigns `x = 1`. The audit mechanically refutes the identity-model
specification rather than assuming it.

No soundness defect was identified in the audited elimination/witness
construction. This conclusion is scoped to the checked semantic model
and the source correspondence below, not a mechanized verification of
the entire C++ implementation.

## Audited source and artifacts

- Revision: `7213ce72bccbd38f35c33cf8c18a6e4336bfe1e3`, PR #11226.
- Implementation: `src/ast/simplifiers/elim_monotone.cpp`.
- Implementation SHA-256:
  `a3a720290d9a4fe7fa3e7f257aa0691e8b0589bbe7e6e677c83bb0fbadf09ae9`.
- Checked module: [`Z3ElimMonotone.fst`](Z3ElimMonotone.fst).
- Related infrastructure inspected:
  `dependent_expr_state.cpp`, `model_reconstruction_trail.h/.cpp`,
  `generic_model_converter.h/.cpp`, and `model_converter.h`.

This module is separate from `Z3SimplifierTheory`'s substitution-congruence
lemma. An eliminated inequality is not equivalent to its replacement
Boolean constant under an arbitrary unchanged interpretation. Likewise,
the recorded assignments are witnesses, not equalities implied by the
input. Applying an equivalence-only substitution theorem here would
prove the wrong specification.

## Checked semantic model

The F* model contains:

- A signature distinguishing real and Boolean constants, an initially
  untyped value map, and an explicit `wf_model` predicate. Thus model
  well-formedness is an obligation, not silently assumed by making every
  assignment a real-valued function.
- Finite affine rows `constant + sum(coefficient * variable)`, with both
  strict and non-strict comparisons against zero.
- Boolean literals/constants, negation, conjunction, disjunction,
  implication, and Boolean ITE.
- A polarity-sensitive elimination operation, finite min/max witness
  construction, and reverse reconstruction of a sequence of eliminations.

Rows use mathematical real coefficients. Rational C++ coefficients embed
into this domain. `coefficient` sums repeated occurrences of a variable;
`lemma_row_split` proves the affine decomposition rather than assuming
that parsing produced the desired polynomial.

`allowed` is an explicit syntactic/affine side condition: all affected
comparisons permit one common direction of movement, Boolean constants
are not overwritten, and an ITE condition is independent of the
eliminated variable. It does **not** assume preservation of satisfiability
or model reconstruction. `valid` checks these conditions at each
intermediate formula in an elimination sequence.

### Main checked obligations

| Obligation | F* theorem |
|---|---|
| Assigning a real value to a real constant preserves model well-formedness | `lemma_put_real_wf` |
| Elimination preserves formula well-sortedness | `lemma_erase_well_sorted`, `lemma_chain_well_sorted` |
| Affine decomposition and independence of the residual from the eliminated variable | `lemma_row_split`, `lemma_residual_update` |
| Finite min/max bounds dominate every affected comparison | `lemma_extreme`, `lemma_bounded_append` |
| Positive occurrences replaced by true and negative occurrences by false weaken the formula in the correct direction | `lemma_weakening`, `lemma_chain_weakening` |
| Min/max plus strict slack forces each removed atom to its required truth value | `lemma_row_witness` |
| Reconstructed values preserve the truth of the enclosing Boolean context, including implication and ITE | `lemma_lift_context`, `lemma_independent_update` |
| Reverse reconstruction yields a well-formed model, with original-formula truth equal to reduced-formula truth | `lemma_chain_reconstruction` |
| Non-eliminated constants retain their interpretations | `lemma_reconstruction_frame` |
| Satisfiability is preserved in both directions | `lemma_equisatisfiable` |
| Reduced models cannot in general be reused unchanged | `lemma_identity_model_counterexample` |
| Zero slack is insufficient for strict bounds; incompatible directions and a dependent ITE condition must be rejected | `lemma_strict_slack_is_necessary`, `lemma_mixed_direction_is_rejected`, `lemma_ite_condition_is_not_eliminable` |

## Witness construction and source correspondence

For an affected normalized atom, write its affine expression as
`c*x + rest`, where `c != 0`, and let `b = -rest/c`.

If all affected occurrences permit increasing `x`, reconstruction chooses
`max(b_1, ..., b_n) + 1`; otherwise it chooses
`min(b_1, ..., b_n) - 1`. Each selected atom is then strictly on its
desired side of zero. This satisfies positive strict/non-strict atoms
and falsifies negative strict/non-strict atoms alike.

| C++ site | Source-level obligation and audit |
|---|---|
| `parse`, lines 59-133 | Accepts real linear comparisons, gathers rational coefficients, removes zero coefficients, and rejects unsupported operations and zero divisors. Unsupported occurrences block their real constants. The mathematical row proof starts after this parsing boundary. |
| `collect`, lines 135-178 | Negation and implication antecedents reverse polarity; conjunction/disjunction and ITE branches preserve it. ITE conditions receive both polarities. Mixed-polarity atoms are rejected and their variables blocked. |
| `pure`, lines 180-183 | Requires an unblocked variable with exactly one nonempty occurrence direction. Updating counts when rows are removed can expose another pure variable. The nonempty direction also ensures the C++ witness has at least one bound, rather than a null `limit`. |
| `bound`, lines 185-202 | Constructs `-rest/c`, omitting the eliminated variable itself. |
| `eliminate`, lines 221-250 | Selects the common direction, folds bounds with min/max, replaces atoms according to polarity, removes their occurrence contributions, and adds one unit of strict slack. |
| Reverse normalization, lines 253-260 | Later witnesses are substituted into earlier witnesses. Previously eliminated variables cannot occur in a still-live row: all their incident rows were removed. This gives the dependency order needed for reverse reconstruction. |
| Formula updates and trail, lines 262-280 | Boolean rewriting follows replacement. The old assertions and dependencies are retained in a `replay_constraints=true` trail entry because witness assignments are not equivalent definitions. |
| `reduce`, lines 286-292 | Freezes protected symbols and bypasses proof-producing goals. |

The actual generic model converter checks that a definition's sort equals
the declaration's range, evaluates definitions with model completion
enabled by default, and installs the resulting interpretations. Its
entries execute in reverse order. These implementation details agree
with the checked witness/reconstruction contract.

### Incremental use

A witness must not be treated as an asserted definition in future queries.
After eliminating `x > 0` with witness `x = 1`, a later assertion `x = 10`
is compatible with the original problem. Permanently imposing `x = 1`
would incorrectly make it inconsistent.

The source uses a loose-constraint trail entry. When new assertions or
assumptions mention an eliminated constant, replay reinstates the
original removed assertions and deactivates that reconstruction entry,
instead of asserting the witness equality. Prefix/dependency/assumption
freezing protects other active uses of a constant. This behavior was
inspected in the C++ and is exercised by the existing
`check_monotone_simplifier` tests, including `x = -1` and `x = 10`.
It is not claimed as a new mechanized proof of the incremental trail.

## Verification

Verified with the installed Linux F* nightly `2026-09-04`,
commit `52f17ab8fdea379708a659a1b02c8f8b47f877fa`, and its bundled
Z3 `4.13.3`. The Windows toolchain path in the shared README was not
available in this environment; no substitute SMT version was used.

From WSL:

```bash
fstar.exe \
  --smt /root/.local/fstar/lib/fstar/z3-4.13.3/bin/z3 \
  --include /mnt/c/z3/fstar \
  --query_stats --z3refresh \
  /mnt/c/z3/fstar/Z3ElimMonotone.fst
```

Result: **all verification conditions discharged**, including a second
run with fresh SMT processes. The module uses `--z3rlimit 10` and contains
no `assume`, `admit`, lax mode, or admitted-query option.

Concrete checks against the built C++ tactic also validated strict lower
bounds, negated comparisons, maximum lower bounds, minimum upper bounds,
cascading witnesses, and Boolean contexts. Reconstructed values were
real-sorted and satisfied every original assertion. Mixed directions
and a dependent ITE condition remained UNSAT. The identity-model
counterexample was reproduced: `x = 0` satisfies the reduced goal, and
the model converter changes it to `x = 1`.

## Remaining trust and coverage boundaries

This is an NFV **semantic source audit**, not extracted/verified C++:

- The F* checker does not execute or translate `parse`, the shared-DAG
  polarity traversal, occurrence counters, AST replacement/rewriting,
  reference counting, or the C++ rational manager. Their correspondence
  to the formal rows and `allowed` precondition is manually reviewed.
- The formal formula language covers affine real/Boolean expressions.
  C++ blocking of variables occurring in unsupported nonlinear terms,
  uninterpreted applications, quantifiers, or protected declarations is
  a source-level boundary, not an additional theorem about those theories.
- The formal well-formed model covers typed real/Boolean constants, not
  every Z3 function/sort interpretation. Other interpretations are
  unchanged by the inspected converter; their complete C++ model
  invariants are not mechanized here.
- Batch reconstruction is checked. Incremental replay, dependency/core
  bookkeeping, cancellation, allocation failure, and the entire tactic
  pipeline are not mechanically verified by this module.
- Trust includes F*, the standard classical/real libraries, their SMT
  encoding, and the pinned SMT backend. No new semantic axioms are added.

These boundaries must not be shortened to a claim that the whole C++
simplifier is formally verified.
