# NFV audit: array index dependencies in PR #11296

## Verdict and audited revision

Issue #11295 reports a real soundness bug, not merely a missing proof
annotation. PR #11296, audited at
`63939b792c0b6121bb80b179db3c73c0777c8f51`, repairs the missing semantic
premises in both the classic SMT and SAT SMT array solvers. No additional
runtime correction was identified in the scoped audit.

The new [`Z3ArrayIndexDependencies.fst`](Z3ArrayIndexDependencies.fst)
provides a mechanically checked countermodel to the old explanation and
proves the corrected finite-domain propagation rule. This is an NFV source
audit: the correspondence to C++ is inspected, not an automatically
verified refinement of the C++ implementation.

## Bug and required explanation

The issue's formula equates a constant-false array over the three-element
datatype `D = {a,b,c}` with:

```smt2
(store (store (store ((as const (Array D Bool)) true)
                     a false) b false) x false)
```

It is satisfiable with `x = c`: every element is overwritten with false.
On a candidate branch where `x = a` or `x = b`, only two domain elements
are written. The chains then disagree at `c`, so the branch must be
rejected.

Before the fix, `same_index` compares current egraph roots and
`add_indices` discards duplicate index tuples. The resulting reduced
count is therefore conditional on branch equalities. The propagated
equality of the constant values records the array-path equalities, but
not the index equalities on which that count depends. The learned
explanation can consequently reject `x = c` as well.

For the branch `x = a`, the valid consequence has the form:

```text
(array-path equalities /\ x = a) ==> false = true
```

Dropping `x = a` makes this implication false. This is a wrong-answer
bug even when proof generation is disabled.

## Mechanically checked obligations

The proof module reuses the extensional `arr`, `store`, and `const_arr`
semantics of `Z3ArrayTheory`. A store chain is outermost-first, matching
the backwards traversal of each reachability path.

| Obligation | F* result |
|---|---|
| Every original index remains semantically covered by the representatives when the recorded equalities hold | `lemma_collect_covers` |
| Recording all non-identical coordinates of an equal-arity tuple establishes equality of its interpreted tuples | `lemma_coordinate_eqs`, `lemma_tuple_dependencies` |
| A distinct list of domain elements longer than the representative list contains an uncovered element | `lemma_covered_size`, `lemma_uncovered` |
| Stores cannot change the base value at an uncovered element | `lemma_chain_uncovered` |
| Two equal chains with too few representative indices have equal base values, conditional on the deduplication dependencies | `lemma_fixed_propagation` |
| The old explanation admits the concrete satisfying `x = c` countermodel while the new dependency excludes it | `lemma_old_omission_countermodel` |
| The `x = a` and `x = b` branches really leave `c` unchanged | `lemma_duplicate_branch_is_conflicting` |
| Checking just one coordinate is insufficient for multi-index equality | `lemma_each_tuple_component_is_needed` |

`collect` models the representative scan and emits one equality for each
discarded tuple. Its proof does **not** assume that root equality is an
unconditional semantic equality: the generated dependencies must hold in
the valuation being considered. Indeed, its coverage theorem works for
any matching predicate, which makes the dependency explicit rather than
hiding the bug in an assumption about egraph roots.

For multi-index arrays, instantiate the index-term carrier with lists of
coordinate terms and interpret tuples component-wise.
`lemma_tuple_dependencies` connects the component equalities actually
recorded by C++ to the whole-tuple dependencies used by the coverage
theorem. Equal tuple arities are a required premise, supplied by
`same_index`'s argument-count check.

The main propagation theorem needs only a distinct **lower-bound** list
of domain elements; it does not assume that list enumerates the entire
domain. Representative values need not be distinct. This avoids assuming
that unequal egraph roots denote unequal model values and also covers
the semantic obligation for large/infinite domains whenever a sufficiently
large finite list is available.

## C++ correspondence

Both implementations make the same substantive correction:

- `src/smt/theory_array_full.cpp:206-230,286-323`
- `src/sat/smt/array_axioms.cpp:804-827,882-912`

`add_indices` now receives the equality vector. Every time `same_index`
allows a store to be omitted, it adds an equality for **each** index
coordinate whose enodes are not literally identical. Omitting identical
enodes is safe by reflexivity. These equalities are retained across both
reachability paths, then augmented with the pre-existing path
equalities before propagating the base-value equality.

The inspected consumers preserve the added dependencies:

- Classic SMT: `ext_simple_justification` copies the enode pairs into the
  context region and `get_antecedents` marks each pair for conflict
  explanation (`src/smt/smt_justification.cpp:319-337`).
- SAT SMT: `array::solver::propagate_axiom` passes the vector to
  `euf::th_explain::propagate`
  (`src/sat/smt/array_solver.cpp:311-318`); the explanation copies the
  pairs into region-owned storage (`src/sat/smt/sat_th.cpp:233-272`).

Thus the fix changes the explanation, not just a diagnostic proof object.
The representative count, domain threshold, and select-internalization
fallback are otherwise unchanged.

## Verification

F* version: `2026.09.27`,
commit `7deb38a27c86990664c6b41e4b6093597acdebd4`.
Both the dependency and audit module verify with warnings treated as
errors. No new axioms, assumptions, admits, or unchecked declarations
are introduced. The existing F* restricted-function extensionality
library remains part of the semantic foundation.

Independent reference-backend verification, from `fstar`:

```powershell
$fstar = 'C:\fstar\fstar\bin\fstar.exe'
$reference = 'C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe'
$cache = '..\build\nfv-cache-reference'
New-Item -ItemType Directory -Force $cache | Out-Null
foreach ($module in 'Z3ArrayTheory.fst', 'Z3ArrayIndexDependencies.fst') {
    & $fstar --smt $reference --z3version 4.13.3 --warn_error '@1..999' `
        --cache_checked_modules --cache_dir $cache --include $cache $module
    if ($LASTEXITCODE -ne 0) { throw "Verification failed: $module" }
}
```

The independently selected Z3 4.13.3 backend discharges all verification
conditions. The candidate checkout was also built and installed for a separate
verification run with an explicitly selected executable, matching
version, and fresh cache:

```powershell
$candidate = '..\build\install\bin\z3.exe'
$cache = '..\build\nfv-cache-candidate'
New-Item -ItemType Directory -Force $cache | Out-Null
foreach ($module in 'Z3ArrayTheory.fst', 'Z3ArrayIndexDependencies.fst') {
    & $fstar --smt $candidate --z3version 5.3.1 --warn_error '@1..999' `
        --cache_checked_modules --cache_dir $cache --include $cache $module
    if ($LASTEXITCODE -ne 0) { throw "Verification failed: $module" }
}
```

The installed solver reports Z3 `5.3.1`, build hash
`63939b792c0b6121bb80b179db3c73c0777c8f51`. Both modules discharge all
verification conditions with this backend as well. The reference and
candidate runs use separate caches; the reference result does not rely
on the candidate solver.

Runtime validation on Windows x64, CMake/Ninja, MSVC, Release:

| Check | Result |
|---|---|
| Build `shell`, `test-z3`, `build_z3_python_bindings` | Passed |
| `test-z3.exe smt_context` | Passed |
| `test-z3.exe /a` | 116 passed, 0 failed |
| Issue input, classic SMT | `sat`, model `x = c` |
| Issue input, `sat.smt=true` | `sat`, model `x = c` |
| Basic integer solving/model, CLI help, locally built Python bindings | Passed |

The existing PR regression covers single-index and two-index arrays,
classic SMT with and without proof generation, and SAT SMT. It checks
SAT without index assumptions, UNSAT under each contradictory index
assumption, inclusion of that assumption in the unsat core, and SAT
again after the assumption is removed.

As a fault-injection check, only the new coordinate-recording loops
were temporarily removed from **both** candidate implementations in
the isolated audit worktree. With all other PR code unchanged, the
issue input returned `unsat` in both engines, and `smt_context` failed
at `core.size() == 1` (`src/test/smt_context.cpp:127`, exit 114).
This independently localizes the missing premise, rather than merely
observing different results from unrelated solver versions.

The exact PR loops were then restored, both targets rebuilt, and the
runtime source diff against the audited PR head checked empty. The
regression passed again, and both engines produced `sat` with `x = c`.
The audit commit adds only the proof module, this report, and the source
audit index entry; no fault-injection changes are retained.

## Trust boundary and exclusions

The proof establishes the semantic rule, the deduplication coverage
invariant, and the coordinate-to-tuple implication. Array-path equality
is a premise of the rule: extraction of the paths and their existing
explanation links is inspected, not formally verified here. The C++
egraph, backtracking, explanation lifetime machinery, sort-cardinality
metadata and bounded multiplication, proof serialization, and overall
array decision procedure are not modeled end to end.

The runtime regressions exercise the actual explanation machinery, but
are not a substitute for an end-to-end verified C++ implementation or
checking every generated proof.
