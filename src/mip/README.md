# Pre-study: a MIP-driven SMT solver core

**Status:** design study, not an implemented solver. Branch: `mip`.
The source inspection is based on commit `68a8a7510`.

## 1. Goal and ownership

Assemble a new solver in `src\mip`, modeled on
`src\sat\sat_solver\sat_smt_solver.cpp`, but reverse the ownership of search:

- The MIP core owns LP relaxations, the branch-and-bound tree, cut generation,
  numeric models, and termination.
- It owns a `sat_smt_solver` as a subordinate Boolean/theory solver, with
  `arith::solver` disabled. It sends Boolean formulas, clauses, cardinalities,
  and assumptions to that subsolver, not numeric constraints.
- Every integer column with a certified domain contained in `{0,1}` has a
  canonical Boolean counterpart. Original Boolean variables and MIP Tseitin
  variables also have binary columns.
- Recognized cardinality rows are represented in both the LP relaxation and
  the SAT subsolver. Arithmetic predicates and conditional arithmetic are
  lowered using justified, row-specific Big-M constants.

This is not an additional arithmetic theory plugin driven by SAT decisions,
and not a wrapper that asks the current arithmetic solver to solve each node.
The subordinate solver may run CDCL internally during a check; it does not own
the MIP tree or choose numerical branch-and-bound splits.

**Recommendation:** start with feasibility for bounded, quantifier-free linear
integer arithmetic plus Boolean/PB structure. This gives a finite search
space and exact integer complements for reification. Extend to mixed
integer/real problems and other SMT theories only after the interfaces below
are validated. Optimization objectives are a later interface: an SMT
feasibility check does not need objective/incumbent pruning.

The initial numeric syntax is affine Int terms (addition, subtraction, and
numeral multiplication), comparisons, and arithmetic `ite`. Variable
products, division/modulus, conversions involving Real, quantifiers, and
mixed-theory numeric terms require separate lowering/support; a broad logic
name must not silently admit operations the core has not implemented.

## 2. What can be reused, and what is missing

| Area | Existing implementation | Consequence for this design |
|---|---|---|
| Solver facade | `src\sat\sat_solver\sat_smt_solver.cpp:116-243,611-731` | Follow its assertion queue, assumptions, scopes, cancellation, model conversion, and result handling; do not copy its SAT-owned search loop. |
| Factory boundary | `src\sat\sat_solver\sat_smt_solver.h:23-25`; `.cpp:733-735` | The concrete class is local to the implementation file, and the factory wraps it in a simplifier solver. Own a `solver_ref`; do not rely on a downcast or private SAT fields. |
| Arithmetic registration | `src\sat\smt\euf_solver.cpp:120-168` | Arithmetic dispatch currently constructs `arith::solver` unconditionally. There is no arithmetic-disable policy on the inspected factory interface. |
| Cardinalities/PB | `src\ast\pb_decl_plugin.h:92-100`; `src\sat\smt\pb_internalize.cpp:38-72,100-225` | Use `pb_util` ASTs and the existing PB/cardinality internalizer, including its reified/non-root path. |
| Cardinality configuration | `src\sat\sat_solver\sat_smt_solver.cpp:331-340` | The wrapper transfers `cardinality.solver` to `keep_cardinality_constraints` and forwards `pb.solver`. Configure these through the existing parameter descriptions. |
| Exact LP | `src\math\lp\lar_solver.h:184-218,322-340,415-424,521-584` | Reuse rational columns, linear terms, bounds, feasibility, scoped state, optimization, and explanations. A row can be represented by a term plus bounds. |
| Integer reasoning | `src\math\lp\int_solver.h:65-103`; `int_solver.cpp:272-302` | Reuse integer-feasibility repair and GCD/HNF/Gomory/branch suggestions. This is not a complete standalone MIP tree manager. |
| Existing consumer of integer moves | `src\sat\smt\arith_solver.cpp:1155-1224`; `src\math\lp\lia_move.h:24-32` | The current consumer turns branches and cuts into SAT atoms. Replace that ownership with MIP nodes and rows; handle every move, including resource exhaustion. |
| Model construction | `src\sat\sat_solver\sat_smt_solver.cpp:655-729`; `src\math\lp\lar_solver.h:467-474` | Merge Boolean and numeric interpretations through explicit mappings and converters, then validate the original assertions. |
| Build assembly | `src\CMakeLists.txt:11-39`; `src\sat\sat_solver\CMakeLists.txt:1-12`; `src\math\lp\CMakeLists.txt:1-54` | A future `mip` component can depend on `solver`, `sat_solver`, and `lp`; add explicit dependencies for directly used AST utilities. |

The APIs are suitable building blocks, but there is currently neither a
MIP-owned coordinator here nor a public subsolver API exposing a resumable SAT
trail. The first implementation should use repeated assumption checks and
unsat cores, not require a new low-level coroutine protocol.

## 3. Proposed component boundary

These are proposed files and interfaces, not existing APIs:

| File under `src\mip` | Responsibility |
|---|---|
| `mip_solver.h`, `mip_solver.cpp` | `mk_mip_solver(ast_manager&, params_ref const&)`, the `solver` facade, node scheduling, results, scopes, and joint models. |
| `mip_internalizer.h`, `mip_internalizer.cpp` | Canonical affine forms, Boolean/gate identities, reification, arithmetic `ite`, and cardinality recognition. |
| `mip_bounds.h`, `mip_bounds.cpp` | Interval bounds, LP-based bound tightening, Big-M certificates, and scope-aware caches. |
| `mip_sat_bridge.h`, `mip_sat_bridge.cpp` | Ownership of the `sat_smt_solver`, assumptions, core-to-clause/row exchange, and model projection. |
| `CMakeLists.txt` | Component assembly once implementation begins. |

Use one `lp::lar_solver` and its associated `lp::int_solver`, not an external
floating-point MIP dependency for the initial prototype. Keep arithmetic
exact and share the AST manager's resource/cancellation budget. Preserve
integer-column metadata while solving the continuous relaxation.
Retain the LP evidence needed for bound/cut provenance even before
user-facing proof production is supported.

Maintain explicit tables for:

1. Original ASTs, normalized expressions, LP columns/terms, and reconstructed
   model terms.
2. Binary columns and their canonical Boolean ASTs, including polarity.
3. Rows, their original assertions/activation guards, and bound/cut evidence.
4. Public assertion scopes, temporary check assumptions, and MIP node scopes.

LP indices and dependency pointers are not persistent assertion identities.
Trail their provenance with their lifetime; store stable source identifiers
or copied certificates when a learned fact must outlive an LP scope.

### Disabling the subordinate arithmetic solver

Add an explicit **internal, opt-in theory-registration policy**, threaded from
the SAT/SMT factory through its internalizer to EUF solver construction.
Preserve the existing factory's default behavior. Under the MIP policy:

- Creating `arith::solver` is forbidden, with an observable invariant/test
  that its creation count remains zero.
- An unexpected arithmetic term is reported as unsupported, never silently
  treated as an uninterpreted term.
- Preprocessing and extensions cannot reintroduce arithmetic unnoticed.
  In particular, integer bit-vector lowering must not create a hidden
  arithmetic subsolver.

Do not approximate this policy with `arith.ignore_int`, and do not simply
return `nullptr` at theory lookup and continue as if the input were handled.

For the first version, abstract **all** numeric predicates before passing
formulas to the subordinate solver. Its assertions contain only Boolean/PB
ASTs and fresh Boolean predicate names; PB coefficients are parameters, not
arithmetic expressions. This restriction makes disabling arithmetic safe.

For later UF/array/datatype integration, Boolean abstraction alone is
insufficient when numerical terms cross theory boundaries. For example,
`x = y` must imply `f(x) = f(y)` even if numeric equality is established only
by the MIP model. A future external-numeric EUF interface must exchange
equalities/disequalities, enforce shared-value arrangements, distinguish
different numeral values, and coordinate model construction without owning
an LP engine. Until that exists, reject those mixed-theory inputs with a
precise `reason_unknown`; do not claim general SMT completeness.

## 4. Binary variables and cardinality compilation

For a registered binary column `x` and counterpart `b`, maintain the invariant
`b <-> x = 1`, with `not b <-> x = 0`. The SAT input uses `b`, not an arithmetic
equality involving `x`.

A domain certificate is mandatory: an arbitrary `Int` is not binary merely
because its current LP value is zero or one. A variable that becomes binary
only under a local bound needs a scoped/guarded registration; its binary
restriction and any deductions using it cannot survive the relevant pop.
Original Boolean variables and Tseitin selectors are binary by construction.

Normalize linear rows before recognizing cardinalities:

- Collect repeated variables and constants. Preserve integer/rational
  coefficients exactly.
- Replace `-x` by `value(not b) - 1` and adjust the threshold.
- After normalization, distinct unit-weight literals give a cardinality.
  Repeated literals that accumulate weight are weighted PB, not a unit
  cardinality.
- Send `sum(lits) <= k` to `pb_util::mk_at_most_k`, and `>= k` to
  `mk_at_least_k`. Equality is the conjunction of the two, or unit-weight
  `pb_util::mk_eq`.
- Compile `sum(lits) >= 1` directly to a clause, and
  `sum(lits) <= n-1` to a clause of complemented literals. Exactly-one is
  an at-least-one clause plus an at-most-one constraint.
- Simplify impossible/trivial thresholds, empty inputs, and unit cases
  **before** converting thresholds to unsigned machine integers.

Retain the corresponding linear rows in MIP to strengthen its relaxation.
Use weighted PB only when coefficients fit the subordinate implementation's
supported representation; its inspected internalizer requires unsigned
machine-sized weights. Do not truncate large coefficients.

Conditional or reified cardinalities remain conditional/reified on both
sides. For example, `g -> sum(x_i) <= k` is not permission to assert an
unconditional at-most constraint in SAT.

## 5. Tseitin conversion and Big-M

Associate a binary column with each MIP-owned Boolean gate and arithmetic
predicate. Assert the gate's Boolean definition in SAT and its linear
encoding in MIP. Assert the top-level Boolean output to one.

### Pure Boolean gates

Use the tight binary-domain specializations of guarded/Big-M encodings:

```text
z = not x:       z = 1 - x
z = and(x_i):    z <= x_i for each i
                 z >= sum(x_i) - (n - 1)
z = or(x_i):     z >= x_i for each i
                 z <= sum(x_i)
clause(l_i):     sum(value(l_i)) >= 1
```

Here `value(b)=x_b` and `value(not b)=1-x_b`. Handle empty `and`/`or`
as constants. These rows avoid generic oversized Big-M values and provide
stronger relaxations than a single aggregate implication row.
Lower implication, equivalence, and XOR through linear-size Boolean gate
networks, or provide independently validated dedicated encodings.

For a Boolean `z = ite(c,p,q)`, use the four guarded inequalities

```text
 z - p <= 1 - c       p - z <= 1 - c
 z - q <= c           q - z <= c
```

The Big-M value one follows exactly from binary bounds.

### Integer arithmetic predicates: encode both directions

After clearing positive denominators, write an integer-valued affine
expression `g(x) = a*x + c` and a selector `z <-> g(x) <= 0`.
Suppose certified bounds over a valid relaxation `P` give
`L <= g(x) <= U`. Then:

```text
M_plus  = max(0, U)
M_minus = max(0, 1 - L)

g(x) <= M_plus * (1 - z)
g(x) >= 1 - M_minus * z
```

When `z=1`, these rows impose the predicate; when `z=0`, they impose its
integer complement `g(x) >= 1`. The inactive inequalities follow from the
certified bounds. A one-way implication is not an encoding of an atom used
under negation, equivalence, or arbitrary Boolean nesting.

Normalize strict integer comparisons using the integer lattice, not a
floating tolerance. GCD normalization and integer rounding can strengthen
the threshold before constructing these rows. An equality uses two
inequality predicates and a Boolean conjunction; its negation is a
disjunction, not the conjunction of the two opposite inequalities.

### Numeric conditional expressions

For `t = ite(z,u,v)`, use separate constants for each residual:

```text
 t - u <= M_tu * (1 - z)       u - t <= M_ut * (1 - z)
 t - v <= M_tv * z             v - t <= M_vt * z
```

Each constant bounds its own affine difference in the inactive case. Do not
assume the same constant is suitable for both signs or both branches.
Derive bounds on the new result column from the alternatives, with scope
and provenance, before attempting this lowering.

## 6. Computing tight Big-M constants

Use a staged, exact procedure, per residual and per activation side:

1. **Normalize.** Combine coefficients first, including cancellation such
   as `x-x`. Track which variables are integer and which bounds are valid.
2. **Interval bound.** For `g=c+sum(a_i*x_i)`:

   ```text
   U_box = c + sum(a_i*u_i for a_i>0) + sum(a_i*l_i for a_i<0)
   L_box = c + sum(a_i*l_i for a_i>0) + sum(a_i*u_i for a_i<0)
   ```

   Retain infinity explicitly. A missing bound is not zero or a large
   sentinel. Row bound propagation can tighten this box cheaply.
3. **LP tightening.** Optimize `g` and `-g` over independently valid rows and,
   when useful, the inactive selector value. Use
   `lar_solver::maximize_term(..., fix_int_cols=false, &dependencies)`.
   Accept an optimized bound/certificate only on `OPTIMAL`. A maximization
   primal value on early termination is a lower bound on the maximum, not
   a safe upper bound for Big-M.
4. **Scope the result.** Global rows may use only globally valid bounds.
   Branch-local tightening produces local rows/cuts or guarded facts.
   Invalidate or restore cached bounds on pop.
5. **Simplify and strengthen.** Propagate an atom whose range proves its
   truth/falsity. Otherwise install the side-specific constants above.
   Budget repeated LP optimization; retain the previous certified bound
   if a tightening attempt is interrupted without a new certificate.

For example, with integer `0 <= x,y <= 10` and an unconditional
`x+y <= 10`, reify `x+y <= 6`. The independent box gives `M_plus=14`.
The LP gives `L=-6`, `U=4` for `g=x+y-6`, hence:

```text
x + y - 6 <= 4 * (1 - z)
x + y - 6 >= 1 - 7 * z
```

These constants are tight for this relaxation, and the integer endpoints
also witness their necessity here.

**Meaning of tight:** interval bounds are tight for the box; optimized bounds
are tight for the chosen LP relaxation, not necessarily for its integer
feasible points. Computing the smallest possible constant over a general
integer feasible set can require solving another MIP. Do not promise that
as routine preprocessing.

Avoid circular certificates: do not bound `g` using the very conditional
row whose M is being justified. Previously validated Big-M rows may be used
for subsequent tightening, but record the derivation order. A bound depending
on an assumption cannot become an unconditional row after that assumption
is removed.

If LP tightening proves a residual unbounded, no finite Big-M is justified.
The first implementation must return `unknown` with a specific explanation
when such a reification is needed. A later exact fallback can branch on a
selector and activate only that branch's rows, retaining explicit indicators
instead of inventing an M. This fallback still belongs to the MIP search.

For Real predicates, `not(g<=0)` is `g>0`, with no uniform positive rational
gap. Do not reuse the integer `1` or a chosen floating epsilon.
`inf_rational` support in the LP is useful but is not by itself a proof of a
guarded strict Big-M encoding: using a tight M with an always-strict row can
exclude the inactive branch's endpoint. Mixed Real support needs a separate
exact strict-indicator design and tests before being enabled.

## 7. MIP-owned search and exchange

At a node, maintain the following contract:

```text
enter node scopes; apply its numeric bounds and Boolean decisions
repeat:
    check SAT under the node's fixed public Boolean counterparts
    if UNSAT: close the node; retain only correctly scoped core consequences
    if UNKNOWN: record an unresolved node, never close it as infeasible

    propagate bounds and solve the LP relaxation
    if certified infeasible: close the node with its explanation
    if interrupted/unsupported: record unresolved, not infeasible

    ask the integer engine for repair, a valid cut, or a split
    if a cut is returned: add it with provenance and repeat
    if a split is needed: create child nodes and return to the scheduler

    obtain an integral candidate for all integer and binary columns
    check SAT under the complete assignment to public binary counterparts
    if UNSAT: import the assumption-core nogood as a linear row and repeat
    if SAT: reconstruct and validate the joint model, then return SAT
    otherwise: preserve UNKNOWN
```

The final candidate check is essential: a satisfiable Boolean completion of
a **partial** cube need not agree with the LP's eventual integer solution.
Conversely, a SAT completion is a branching hint, not an inferred numeric
bound that can be permanently asserted.

An infeasible binary assignment core `l_1,...,l_k` yields the clause
`not l_1 or ... or not l_k` and the row
`sum(value(not l_i)) >= 1`. Its validity depends on the subordinate solver's
current assertion context; keep activation guards or the corresponding
scope when exporting it. This avoids needing private SAT variable IDs.

The first bridge can obtain additional sound propagation by checking
`cube and not b`: an UNSAT result proves `b` under `cube`, not globally.
Later, existing fixed/final/clause callbacks can reduce repeated checks,
but their SAT-internal decision scopes must not be confused with MIP nodes.
Do not export a learned clause with unmapped SAT-private auxiliaries as if
all its literals already had MIP columns.

For a fractional general integer `x=v`, split into
`x <= floor(v)` and `x >= floor(v)+1`. These children cover every integer
possibility. Binary branching is `x=0` versus `x=1`. Decode the integer
engine's returned term, offset, orientation, and explanation; it is not
always a single-variable bound. Start with GCD/Gomory cuts through
`lp::int_solver`, then evaluate HNF and other mechanisms. Avoid an
unbounded cut-generation loop by budgeting cuts and scheduling a valid split.

Arithmetic infeasibility may prune a MIP node without producing a SAT clause.
Export a clause only if every required assumption/row dependency has a
valid Boolean explanation; never drop numeric branch conditions to make
an explanation look global.

Return UNSAT only after all covering branches are closed by valid conflicts
or cuts, with no unresolved nodes. The bounded-integer initial fragment can
also use fair branching over finite domains to guarantee eventual search
exhaustion in the absence of resource limits.

## 8. Incrementality, models, and supported results

- Trail original assertions, normalizations, mappings, rows, binary domain
  certificates, Big-M caches, and SAT assertions together at public scopes.
  Keep temporary check assumptions and internal node scopes separate.
- A local cut/M may remain local. A retained global cut needs a global
  derivation or explicit guards. Pop must remove dependencies before their
  identifiers can be reused.
- The SAT factory includes a simplifier/model converter. Preserve its
  reconstructed Boolean values and protect the identity of external bridge
  variables through assumptions/conversion. Never assume a missing Boolean
  model entry is an unconstrained zero-valued numeric column.
- Build original numeric interpretations from the exact LP integer candidate,
  merge the consistent subordinate model, apply preprocessing substitutions
  in the correct direction, and hide fresh gate/selector symbols.
- Before reporting SAT, evaluate the original assertions and assumptions in
  the joint model. A failed or incomplete validation is not SAT.
- For UNSAT cores, track original assertions and branch coverage; one node's
  infeasibility core is not a core for the whole search.
- Proof production needs certificates for lowering, bound optimization,
  integer cuts, and branch closure, composed with subordinate SAT proofs.
  Initially expose no proof support and reject unsupported proof requests
  explicitly. Do not claim unsat-core support until reconstruction is tested.
- Keep the solver opt-in behind a new factory/tactic. Do not change default
  SMT, SAT/SMT, or optimization selection in the first implementation.

## 9. Staged implementation and validation

1. **Facade and bridge.** Add the component/factory, registration policy, and
   a Boolean/PB-only subsolver. Implement scopes, assumption checks, and
   explicit unsupported-feature/resource results.
2. **Exact bounded linear fragment.** Add affine normalization, binary
   counterparts, LP rows, Boolean gates, two-sided integer reification,
   numeric conditionals, and domain/bound certificates.
3. **MIP search.** Add explicit node management, integer splits, scoped cut
   insertion, SAT-core nogoods, and validated joint models.
4. **Tightening and performance.** Add selective LP bound optimization,
   stronger cardinality/PB exchange, cut/node heuristics, and statistics.
5. **Broader SMT/Real support.** Design exact unbounded/strict indicators,
   shared numeric EUF interfaces, and certificate/core composition before
   advertising those capabilities.

Focused correctness tests should include:

- Exhaustive small Boolean truth tables for gate encodings and reified
  cardinalities; negative literals, duplicates, empty inputs, threshold
  extremes, large coefficients, and clauses recognized from rows.
- Two-sided predicate checks at the integer threshold and its complement;
  rational scaling, negative coefficients, equality/disequality, and both
  branches of arithmetic `ite`.
- Big-M bounds from boxes versus correlated LP constraints, constant and
  canceled residuals, missing/infinite bounds, interrupted optimization,
  and forbidden self-justifying or branch-leaked bounds.
- A satisfiable partial SAT cube whose selected integral MIP assignment is
  rejected, and a valid SAT-core nogood that forces another numeric candidate.
- Fractional LP solutions requiring branching; cuts requiring local
  assumptions; complete tree exhaustion; and cancellation on either side.
- Push/pop after local binary-domain discovery or tighter M computation,
  repeated checks with changing assumptions, and stable source provenance.
- Joint-model validation and the invariant that no subordinate
  `arith::solver` is instantiated, including through preprocessing.
- Differential tests against existing Z3 solvers and exhaustive bounded
  enumeration. Add shared-numeric UF counterexamples before extending the
  admitted theory combination.

Measure nodes, LP solves/pivots, integer repairs, cut attempts/acceptance,
SAT checks and core sizes, imported cardinalities/clauses, bound-tightening
time, Big-M distributions, and model-validation failures. Compare SAT/PB-only
baselines and bounded LIA cases against both the existing SMT and SAT/SMT
engines. Report timeouts and unsupported cases separately from solved cases.

This branch intentionally adds only the pre-study. There are no solver,
parameter, build, or default-behavior changes yet.
