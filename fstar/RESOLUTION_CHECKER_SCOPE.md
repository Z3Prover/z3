# Scoping a resolution/clausal proof-step checker

## Motivation

Sampling real Z3 `(get-proof)` output on QF_AX/QF_UF benchmarks (see
"Coverage report" below) shows that the equational rewrite-calculus
modeled by `Z3ProofTheory.fst`/`Z3PatternMatchedProofChecker.fst`
(`Refl`/`Sym`/`Trans`/`Congr`/`Rewrite`/`QuantIntro`) is only a small
island inside a much bigger proof DAG. The rest of the DAG is built
from Z3's *propositional/clausal* calculus: `unit-resolution`,
`monotonicity` (on `Bool`, not just equalities), `mp` (modus ponens),
`trans`/`trans*`, `and-elim`, `hypothesis`/`lemma`, `commutativity`,
`def-axiom`, `th-lemma`, `array-ext`, `hyper-resolve`. None of these
are visible to the existing equational-only checker: our Python
extraction pipeline (`extract_z3_proof.py`) only walks the subtree
rooted at the single equational "root" it can find and flattens
anything it doesn't recognize into an opaque `Rewrite` leaf. This
document scopes a new proof-term layer, `Z3ResolutionProofTheory.fst`,
that sits *above* the equational calculus and models these
clausal/propositional rules directly, with Z3's own
`src/ast/proofs/proof_checker.cpp::check1_basic` as the ground-truth
executable specification for each rule's acceptance condition.

## Rule inventory, tiered by how precisely they can be mechanized

**Tier 1 — fully mechanized (soundness proved as an F* lemma, generic
over any interpretation satisfying the stated side hypotheses):**

| Rule | `proof_checker.cpp` semantics | F* status |
|---|---|---|
| `PR_UNIT_RESOLUTION` | clause `(or l0..ln)` + resolvent proofs of literals complementary to some `li`; conclude the surviving disjunction, or the single survivor, or `False` | `lemma_clause_shrink` + `lemma_unit_resolution_sound` (new) |
| `PR_AND_ELIM` | `(and t1..tn)` true `=>` each `ti` true | `lemma_and_elim_sound` (new) |
| `PR_NOT_OR_ELIM` | `not(or l1..ln)` true `=>` each `not li` true | `lemma_not_or_elim_sound` (new) |
| `PR_MODUS_PONENS` / `PR_MODUS_PONENS_OEQ` | `a`, `a => b` (or `a <=> b`) `=>` `b` | `lemma_mp_sound` (new) |
| `PR_COMMUTATIVITY` | `f` commutative `=>` `f(s,t) = f(t,s)` | `lemma_commutativity_sound` (new) |
| `PR_IFF_TRUE` / `PR_IFF_FALSE` | `a` true (resp. `not a` true) `=>` `(iff a true)` (resp. `(iff a false)`) | `lemma_iff_true_sound`/`lemma_iff_false_sound` (new) |
| `PR_REFLEXIVITY`/`PR_SYMMETRY`/`PR_TRANSITIVITY`/`PR_MONOTONICITY` (eq case) | — | already modeled (`Z3ProofTheory.fst`'s `Refl`/`Sym`/`Trans`/`Congr`), embedded here as a leaf |
| `PR_HYPOTHESIS` + `PR_LEMMA` | a branch assumes `not fact` as a hypothesis; a later `lemma` node discharges `False` under exactly that (and only that) hypothesis set, concluding `fact` | `lemma_discharge_sound` (new): classical "proof by contradiction" shape, hypothesis list must be empty at the root |
| array extensionality (`array-ext`, not in `check1_basic`'s basic-family switch at all — see below) | `a = b <=> forall i. select(a,i) = select(b,i)` | `lemma_array_extensionality` *already proved* in `Z3ArrayTheory.fst`; now exposed as a resolution-layer leaf, `ArrayExt` |

**Tier 2 — trusted leaves (the obligation is recorded as an explicit
side-condition `expr`, exactly as Z3's own checker does — see below —
not independently re-derived):**

| Rule | Why Tier 2 |
|---|---|
| `PR_DEF_AXIOM` | `check1_basic`'s own case is `match_fact(p) && m.is_bool(fact)` — i.e. *any* Boolean fact is accepted; Z3 trusts the SAT solver's CNF/Tseitin encoding here, we do the same |
| `PR_TH_LEMMA` outside the checked array fragment below | dispatches to `check_arith_proof` only for the `"arith"` theory tag; every other theory (including `"array"`) falls through to `dump_proof(p); return true` — i.e. **Z3's own in-tree checker does not verify array theory lemmas either** |
| `PR_HYPER_RESOLVE` | `check1_basic` computes a side-condition formula (`premise0 <=> conclusion`) and pushes it to `side_conditions` rather than proving it |
| `PR_REWRITE_STAR` / `PR_DISTRIBUTIVITY` | same pattern: `side_conditions.push_back(fact)` |
| `PR_QUANT_INST` | literally `// TODO return true` in `check1_basic` |
| Any non-`basic`-family proof node (e.g. the array-theory-plugin's own proof rules) | `proof_checker::check1` only dispatches `get_basic_family_id()`; every other family (`check1_spc` included) is `#if 0`'d out / returns `false` — i.e. genuinely outside what Z3's checker itself ever validates |

This tiering is not a weaker standard than Z3's own: Tier 2 above is
*exactly* the set of rules Z3's own `proof_checker.cpp` either trusts
unconditionally or defers to an unverified side condition. Modeling
them as `Trusted` leaves with an explicit obligation expression (never
silently assumed `True`) is strictly more transparent than that
baseline, since the obligation remains visible for a future pass to
discharge via a theory-specific soundness lemma, exactly the way
`Rewrite` leaves already are for the equational layer.

The executable's `def-axiom` policy now trusts premise-free Boolean leaves
without counting them as pending obligations. The optional
`--check-original-assertions` mode instead requires exact membership of
each whole conclusion in the supplied original assertions. This differs
from independently validating Tseitin transformations; the default
soundness theorem explicitly assumes trusted definitions hold.

`PR_TRANSITIVITY_STAR`'s cycle-basis argument (XOR-insert over vertex
ids, see `check1_basic`) is deferred past this first round: it needs
an auxiliary graph argument, not just structural induction; noted here
as a concrete next-round target, not modeled in `Z3ResolutionProofTheory.fst` yet.

## Architecture

New module `Z3ResolutionProofTheory.fst`, opening `Z3AstTheory` and
`Z3ValueTheory` and reusing `Z3ProofTheory`'s `proof`/`is_not`:

```
type literal = expr
type clause  = list literal

let rec clause_holds i rho (c:clause) : prop =       (* "(or ...)" is true *)
  match c with [] -> False | l :: c' -> lit_true i rho l \/ clause_holds i rho c'

let rec conj_holds i rho (c:list expr) : prop =       (* "(and ...)" is true *)
  match c with [] -> True | l :: c' -> lit_true i rho l /\ conj_holds i rho c'

noeq type rproof =
  | Eq        : p:Z3ProofTheory.proof -> rproof              (* embeds the equational layer unchanged *)
  | UnitRes   : clause:clause -> cl_pf:rproof -> lits:list (expr & rproof) -> rproof
  | AndElim   : conj:list expr -> idx:nat -> pf:rproof -> rproof
  | NotOrElim : disj:list expr -> idx:nat -> pf:rproof -> rproof
  | ModusPonens : a:expr -> b:expr -> pf_a:rproof -> pf_imp:rproof -> rproof
  | Commute   : f:func_decl -> s:expr -> t:expr -> rproof
  | IffTrue   : a:expr -> pf:rproof -> rproof
  | IffFalse  : a:expr -> pf:rproof -> rproof
  | ArrayExt  : a:expr -> b:expr -> idx_sort:sort -> rproof              (* new Tier-1 rule *)
  | Hyp       : a:expr -> rproof                                         (* PR_HYPOTHESIS *)
  | Discharge : hyps:list expr -> pf_false:rproof -> fact:expr -> rproof (* PR_LEMMA *)
  | Trusted   : tag:string -> obligation:expr -> rproof                  (* Tier 2 *)
```

`rfact : rproof -> option expr` (the single concluded formula, mirroring
`Z3ProofTheory.fact`'s `option (expr & expr)` but for a bare Boolean
fact rather than an equation), and `all_rtrusted_sound i p : prop`
(generic analogue of `all_leaves_sound`, now also walking `Eq`'s nested
equational proof and requiring every `Trusted tag obligation` leaf's
`obligation` to hold under `i`). Target theorem:

```
lemma_rproof_sound (i:interpretation value) (p:rproof) (rho:env value)
  : Lemma (requires Some? (rfact p) /\ all_rtrusted_sound i p /\ hyps_closed p [])
          (ensures lit_true i rho (Some?.v (rfact p)))
```

`hyps_closed p open_hyps` tracks, exactly as Z3's own (currently
`// TBD`) invariant does, that every `Hyp a` leaf reachable in `p` is
discharged by an enclosing `Discharge` whose `hyps` list contains `a` —
i.e. no proof is accepted with a *dangling* hypothesis. This closes the
one gap `proof_checker.cpp` itself leaves as a comment (`PR_HYPOTHESIS`:
"TBD all branches with hypotheses must be closed by a later lemma").

## Executable integration

`tools/extract_z3_proof.py --full-proof` exports the complete ground DAG
to `Z3ResolutionProofJson.fst`'s native-checker path, including resolution,
MP (including `mp~`), `iff~`, congruence, and hypothesis discharge.
Both `refl` (Z3's emitted spelling) and `reflexivity` check reflexivity.
The decoder uses `Z3UnifiedProof.fst`'s common proof nodes with tagged
`Holds`, `Equal`, and `Observational` judgments. It no longer wraps
already-checked facts in synthetic legacy proofs. The unified inference
and scoped-node checkers have common soundness theorems, reusing the
existing theory-specific semantic lemmas. Legacy recursive proof types
remain available but are not constructed by this full-DAG path.
Observational equality retains its separate `~`/`op_oeq` representation
and `Observational` judgment. `mp~` checks its own
relation; `iff~` is an explicit one-way bridge from Boolean equality.
Observational symmetry/transitivity/congruence never yield ordinary
equality. The ground semantic theorem covers observation-preserving
steps; general naming/Skolemization witnesses are not silently assumed.
`RUnitRes` accepts scalar and
empty-clause representations as well as reordered/weakened consequences
that retain every surviving literal. The total identity rewrite rule
discharges syntactically identical endpoints. Verified n-ary Boolean
`and`/`or` flattening splices nested occurrences of the same connective
without changing operand order or multiplicity. The additional verified
Boolean normalizer proves n-ary De Morgan, implication elimination,
double negation, contextual ACI, singleton collapse, constants,
complements, and absorption. Reflexive equality reduces to `true` at
any sort. A native-tag Boolean skeleton also connects the verified
general-purpose truth-table checker to the kernel, with depth 8 and at
most 10 opaque atoms (1,024 rows); structural normalization has no atom
limit and uses fuel 32 for contextual set comparison. No equality of
distinct non-Boolean theory atoms is assumed. Unsupported rules,
non-equivalences, and checks exceeding the supported fragment/budgets
remain explicit obligations (`PARTIAL`, exit 3); rule-name classification
does not certify them. See `OCAML_CHECKER_REPORT.md` for usage, the
58-proof QF_UF recheck, and the fresh 100-file-per-logic QF_UF/QF_AX
evaluation with separate proving, export, and checking limits.
Both native JSON formats cache per-node results by numeric proof ID and
never recursively recheck shared premises. The legacy cache's result is
F*-proved equal to `fact` of its stored proof, including failed results;
the full-proof cache retains each fact's hypothesis scope. Expressions
also use an indexed cache instead of linear prefix lookups. References
must point backward, so cycles and incomplete-cache hits are rejected.
`commutativity` is checked by `Z3Commutativity.fst` for binary equality,
Boolean `and`/`or`, and `Int` addition/multiplication. The checker validates
declarations, sorts, and exact swapped endpoints; its soundness follows
from standard theory semantics, not an assumed commutativity property.
Unsupported theories remain obligations in exported documents.
The default extractor mode remains the legacy equational fragment.

### Checked SMT array theory instances

`Z3ArrayTheory.fst` now covers the store, extensionality, lambda,
congruence, constant, as-array, n-ary map, default, and choice axiom
schemas instantiated by `src\smt\theory_array_base.cpp` and
`theory_array_full.cpp`, with explicit witness/freshness conditions.
Multi-index mathematical instances use tuple indices. Default-store
invariance is conditional on a fresh epsilon index; the singleton and
finite non-singleton cases have separate lemmas. An extensionality
index must witness an actual difference, and choice requires a
satisfying value only when the predicate is satisfiable.

`Z3ArrayLemma.fst` promotes three premise-free `th-lemma` schemas from
pending obligations to checked nodes: read-over-write at the written
index, guarded read-over-write at another index, and the extensionality
clause using the built-in difference index. It checks full operator
declarations and sorts, not merely names or the proof-rule label.
The `array-ext` declaration carries `op_array_ext`; uninterpreted
lookalikes and arbitrary/unrelated witnesses remain obligations.
`lemma_array_lemma_sound` composes the array lemmas with the shared
kernel's explicit `array_model` interpretation contract.

Native matching currently covers flat one-dimensional arrays of
non-Boolean scalar indices/elements in the existing `VArr`/`VInt`
semantics. The broader mathematical schemas do not imply executable
support for Boolean/nested/multi-index arrays, map/default/choice, or
quantified expressions. These remain unsupported or pending, and
`def-axiom` trust is unchanged. See `OCAML_CHECKER_REPORT.md` for the
axiom-to-lemma catalog and paired evaluation: QF_AX increases from
1 to 70 accepted proofs and QF_AUFLIA from 1 to 28 per 100 sampled files.
The associated proved `not-or-elim` polarity correction also removes
structural rejections in the arithmetic samples.

## Status after round 1 (implementation complete, fully verified)

`Z3ResolutionProofTheory.fst` compiles and **all verification conditions
discharge successfully** (`fstar.exe`, no `admit`, no timeouts, ~4.6s
total). Final content:

- **Semantic layer** (interpretation-generic, parametrized by explicit
  connective-soundness hypotheses `not_sound`/`and_sound`/`or_sound`/
  `implies_sound`/`eq_sound`/`true_sound`/`false_sound`, mirroring
  `quant_extensional`'s existing style): `clause_holds`/`conj_holds`/
  `lit_true`/`lit_is_false`, `complementary` (+ `lemma_complementary_sym`),
  `lemma_complementary_sound`, `remove_first`/`lemma_clause_shrink`
  (using `FStar.Classical.excluded_middle`/`or_elim` for the classical
  case split Z3's own checker takes for granted), `wf_clause` (the
  explicit well-sortedness side condition — every clause literal is
  Boolean-valued — needed because `interpretation`'s `eval` is not
  a priori known to be Boolean-sorted on arbitrary `expr`s),
  `find_complement`/`lemma_find_complement_mem`, `unit_resolve`/
  `lemma_unit_resolve_sound`/`lemma_unit_resolution_sound` (the full
  n-ary `PR_UNIT_RESOLUTION` fold), `lemma_and_elim_sound`,
  `lemma_not_or_elim_sound`, `lemma_mp_sound`, `lemma_commutativity_sound`,
  `lemma_iff_true_sound`/`lemma_iff_false_sound`, `lemma_array_ext_sound`
  (thin wrapper around the already-proved
  `Z3ArrayTheory.lemma_array_extensionality`).
- **Proof-term layer**: `rproof` (`REq`/`RAndElim`/`RModusPonens`/
  `RCommute`/`RIffTrue`/`RIffFalse`/`Trusted`), `rfact`, `all_rtrusted_sound`,
  and the composed theorem `lemma_rproof_sound`, proved by structural
  induction exactly mirroring `Z3ProofTheory.fst`'s `fact`/
  `all_leaves_sound`/`lemma_proof_sound` pattern.

Two design corrections made while debugging to verification (recorded
since they are non-obvious and would recur if this file is extended):
1. `not_sound`/`eq_sound`/etc. must be given explicit `{:pattern ...}`
   SMT triggers that bind *all* quantified variables (e.g. `not_sound`'s
   pattern is `eval i (App f [a]) rho`, binding `f`/`a`/`rho` but *not* a
   separate witness `b:bool` — the original draft's extra `b` parameter
   made the pattern reject with "misses at least one bound variable").
   Stating `not_sound` as a direct `<==>`-shaped fact (no existential
   witness) avoided needing a `VBool?`/projector precondition entirely.
2. `rfact`'s internal use of list membership must use the *decidable*
   `FStar.List.Tot.Base.mem` (`Tot bool`), not `memP` (`Type0`/`prop`) —
   using `memP` inside a `Tot` function's boolean guard silently forces
   the whole function into the `GTot` effect, which then fails to check
   against its own `Tot` return-type annotation. `FStar.List.Tot.
   Properties.mem_memP`'s `[SMTPat ...]` bridges the two forms
   automatically wherever a lemma needs the `prop` form instead.
3. The original `Trusted : tag:string -> obligation:expr -> fact_:expr`
   constructor had no structural link between `obligation` (what
   `all_rtrusted_sound` requires to hold) and `fact_` (what `rfact`
   claims as the conclusion) — nothing forced them to denote the same
   formula. Collapsed to a single `concl:expr` field.
4. `FStar.StrongExcludedMiddle` is not available in this F* installation's
   `ulib`; `FStar.Classical.excluded_middle`/`or_elim` is the supported
   replacement for the classical case split `lemma_clause_shrink` needs.

`PR_HYPOTHESIS`/`PR_LEMMA`'s hypothesis-discharge bookkeeping
(`Hyp`/`Discharge`, `hyps_closed`) and promoting `unit_resolve`/
`and_elim`/`not_or_elim` into first-class `rproof` constructors (so a
single `rproof` term can represent an entire real resolution refutation,
not just the propositional-glue steps around one rewrite island) remain
open for a follow-up round — see "Round 2 candidates" below.

## Coverage measurement methodology

`tools/proof_rule_coverage.py` (new) walks the *entire*
raw Z3 proof DAG for each benchmark (not just the equational island
`extract_z3_proof.py` finds) and classifies every proof-rule-name
occurrence (deduplicated by node id) into Tier 1 / Tier 2 / Unmodeled
per the table above, then reports, per benchmark set, the fraction of
total proof nodes and the fraction of *benchmark files* whose entire
proof is within Tier 1 ∪ Tier 2 (i.e. nothing structurally unmodeled).
See `RESOLUTION_CHECKER_REPORT.md` for results.

## Round 2 candidates (status: done)

Round 2 promotes the three standalone lemmas named in the "remain open"
note above into first-class `rproof` constructors, and adds explicit
hypothesis-discharge bookkeeping, closing the gap `proof_checker.cpp`
itself flags ("all branches with hypotheses must be closed by a later
lemma"):

- `RUnitRes : or_f:func_decl -> disj:clause -> clause_pf:rproof ->
  units:list (expr & rproof) -> rproof` — `PR_UNIT_RESOLUTION`.
  `clause_pf` proves `(or disj)`; `units` pairs each unit-resolvent
  literal with the sub-`rproof` establishing it; the conclusion is the
  residual clause from `unit_resolve` (already proved sound in round
  1), re-wrapped in `(or ...)`. Checked via a new 3-way mutual
  recursion `rfact`/`rfacts_match`/`lits_of` (mirroring
  `Z3ProofTheory.fst`'s `fact`/`facts_of`), and a matching
  `all_rtrusted_sound_units`/`hyps_closed_units` pair.
- `RNotOrElim : t:expr -> premise:rproof -> rproof` — `PR_NOT_OR_ELIM`.
  `disj` is *not* stored as a field; it is recovered structurally by
  pattern-matching `premise`'s own fact `(not (or disj))` — the same
  "minimal field" style `RIffFalse` already used in round 1.
- `Hyp : a:expr -> rproof` — `PR_HYPOTHESIS`. Licensed only when `a` is
  a member of the ambient hypothesis list threaded through the new
  `hyps_closed p hyps` side condition.
- `RLemma : fact_:expr -> pf_false:rproof -> rproof` — `PR_LEMMA`.
  Classical proof by contradiction: `pf_false` must prove `false_expr`
  under *exactly* the single local hypothesis `(not fact_)`
  (`hyps_closed pf_false [mk_not_expr fact_]`, checked as a side
  condition in `all_rtrusted_sound`, not against the ambient ⁠`hyps`
  the `RLemma` node is itself embedded under — it is a self-contained,
  locally closed sub-derivation). Conclusion is `fact_`, unconditionally.

The top-level theorem generalizes from `lemma_rproof_sound i p rho`
(no open hypotheses) to `lemma_rproof_sound_hyps i p rho hyps`, with
conclusion `conj_holds i rho hyps ==> lit_true i rho (Some?.v (rfact
p))` — an implication rather than a bare fact, needed so `RLemma`'s
hypothetical reasoning threads through. `lemma_rproof_sound` is kept
as a convenience corollary: `lemma_rproof_sound_hyps i p rho []`
(trivial, since `conj_holds i rho [] == True`).

Lessons learned debugging this round:

1. **Never name an `rproof` constructor `Lemma`.** F*'s `Lemma`
   effect/type is a bare, unqualified top-level identifier; a
   same-named data constructor shadows it completely, and every
   subsequent `: Lemma (requires ...) (ensures ...)` signature in the
   file fails to parse with confusing, unrelated-looking errors
   ("Expected type `Z3AstTheory.expr` but ... has type `Prims.prop`",
   "Expected type `rproof` but ... has type `Prims.prop`") rather than
   a shadowing complaint. Renamed to `RLemma` (matching the existing
   `R`-prefixed-constructor convention) and the errors vanished
   immediately.
2. **`Classical.impl_intro : (squash p -> Lemma q) -> Lemma (p ==> q)`**
   is the right tool to thread the ambient `hyps` hypothesis through
   every branch of `lemma_rproof_sound_hyps` uniformly: each branch
   wraps its (otherwise unchanged, round-1-style) proof body in `let
   aux (_:squash (conj_holds i rho hyps)) : Lemma (post) = <old body>
   in Classical.impl_intro aux`, with no need to restructure any
   individual branch's internal reasoning.
3. The `RLemma` case's own soundness obligation is checked via a
   standalone (non-mutually-recursive) helper, `lemma_lemma_sound`,
   taking the *already-established* fact
   `conj_holds i rho [mk_not_expr fact_] ==> lit_true i rho false_expr`
   (obtained by the caller via a prior call to
   `lemma_rproof_sound_hyps i pf_false rho [mk_not_expr fact_]`) as an
   explicit `squash`-typed argument, then classically case-splits
   (`Classical.excluded_middle`/`or_elim`, same idiom as round 1's
   `lemma_clause_shrink`) on whether `(not fact_)` holds at `rho`.
4. Compiled clean on the first attempt after the naming fix — no
   further SMT-side tuning (triggers, fuel/ifuel) was needed beyond
   what round 1 already established.

Verified: `fstar.exe --query_stats Z3ResolutionProofTheory.fst` — 0
errors, "All verification conditions discharged successfully".
