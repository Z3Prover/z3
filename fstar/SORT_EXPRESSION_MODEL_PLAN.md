# Sort and Expression Model: Review and Implementation Plan

Date: November 6, 2026

Status: proposed implementation plan. This report does not change the model,
the checker routes, or the supported SMT fragment.

## Recommendation

Use structured syntax for understood sorts, with an explicit extension
constructor and opaque declaration identities for other sorts. Interpret that
syntax through sort-indexed semantic carriers. Keep executable structural
equality of sorts and expressions separate from semantic equality of values.

Build on the existing typed-root prototype rather than introducing another
parallel semantic framework. Promote its capabilities into production only
after proving the required checker correspondence and enforcing its support
checks at the native entry points.

Strings remain suitable for display names and, with an injectivity invariant,
opaque identifiers. They should not be the only representation of interpreted
sort structure.

## 1. Findings in the current implementation

### 1.1 Sort syntax preserves less information than the native AST

`Z3AstTheory.fst` defines:

```fstar
type sort =
  | BaseSort  : name:string -> sort
  | ArraySort : domain:list sort -> range:sort -> sort
```

Arrays have recursive, multi-index structure. Other sorts are represented as
names. For example, `Z3BvLemma.bv_sort` encodes a width as `"BV" ^ string_of_int
width`; `Z3FiniteFieldLemma.ff_sort` uses an analogous field-modulus encoding.

The OCaml and Cherry bridges distinguish built-in sorts and qualify otherwise
opaque names with native sort IDs. This is stronger than using display names
alone. Nevertheless, the model cannot structurally inspect the element sort of
a sequence or the parameters of an opaque datatype instance.

String encodings also introduce unnecessary proof work: `Z3StandardModel.fst`
documents bounded BV-width decoding and the difficulty of proving general
`string_of_int` injectivity.

Relevant sources:

- `Z3AstTheory.fst`: `sort`, `sort_eq`, `func_decl`, `expr`, `wf`.
- `Z3BvLemma.fst`: `bv_sort`.
- `Z3FiniteFieldLemma.fst`: `ff_sort`.
- `Z3StandardModel.fst`: width decoding and its documented bound.
- `ocaml_runtime\Z3Native.ml`: `view_sort`, `logical_sort`.
- `cherry_runtime\native.cpp`: `view_sort`, logical-sort construction.
- `..\src\ast\ast.h`: native declaration families, kinds, and parameters.

### 1.2 Array-valued elements already work in the core theory

`Z3ArrayTheory.fst` defines:

```fstar
type arr (idx:eqtype) (v:Type) = idx ^-> v
```

The value parameter is `Type`, not `eqtype`. Consequently, an array can already
be the element type of another array in this theory. Basic read-over-write
and extensionality lemmas likewise admit arbitrary value types.

There are three separate restrictions to address:

| Layer | Current restriction | Consequence |
|---|---|---|
| Core array theory | Index type is `eqtype` | Does not cover arbitrary semantic index carriers, including function-valued arrays |
| Some helper lemmas | Value type is also `eqtype` | Cannot instantiate these helpers with array-valued elements |
| Shared concrete value domain | `VArr` contains only `arr int int` | Concrete interpretation does not compose nested arrays |

`Z3ArrayLemma.fst` additionally recognizes only single-index arrays with flat,
non-Boolean index and element sorts. Widening its recognizers without changing
the supporting semantic contracts would not establish broader SMT coverage.

### 1.3 Sequence theory is generic; the concrete interpreter is specialized

`Z3SeqTheory.fst` models lists over an arbitrary `eqtype`. By contrast,
`Z3ValueTheory.VSeq` contains `seq int`, and `Z3SeqInterp.fst` builds sequence
units only from `VInt`.

This is a specialization to integer sequences, not a general character model.
The comment in `Z3SeqTheory.fst` describing string characters as 8-bit
bit-vectors is stale: the native sequence plugin uses the dedicated character
plugin and constructs strings over that character sort.

The standalone regex expression model also uses a single `BaseSort "Seq"`
marker. It should eventually distinguish sequence element sorts rather than
treating every sequence instantiation as one marker.

### 1.4 The typed-root prototype already demonstrates the main repair

`Z3TypedRoot.fst` defines carriers by sort, including Bool, Int, Real, and
restricted ghost function spaces for arrays. Array indices are tuples of
carriers, supporting multi-index arrays. Ghost equality permits functional
updates without requiring a computational equality decision for every carrier.

`Z3TypedRootTests.fst` includes nested read-over-write for
`Array Int (Array Int Real)`, as well as multi-index examples.

Important boundaries remain:

- Typed-root modules are registered as tests, not production checker modules.
- BV, FF, sequence, and other base sorts remain uninterpreted in this prototype.
- Arrays involving datatype sorts are outside its supported fragment.
- Production routes do not enforce the prototype's support predicates.

Therefore, the prototype is a reusable foundation, not evidence that production
checking already supports all these combinations.

## 2. Target design and invariants

### 2.1 Structured, extensible sort syntax

Introduce explicit constructors for the supported interpreted families:

```text
Bool
Int
Real
Char
BitVec(width)
Array(nonempty index_sorts, element_sort)
Seq(element_sort)
RegEx(sequence_sort)
FiniteField(modulus)
FiniteSet(element_sort)
Datatype(declaration_id, instantiated_sort_arguments)
Uninterpreted(declaration_id, instantiated_sort_arguments)
Extension(family_key, kind_key, typed_parameters)
```

This is a design sketch, not an F* declaration. In particular:

- Use declaration identities, not display names, for uninterpreted sorts and
  datatype declarations. Scope those identities to a model/document context.
- Preserve the distinction between an n-index array and nested unary arrays;
  do not silently curry or flatten sorts during import.
- Identify datatype instances by their declared type parameters, not by a list
  of non-recursive field sorts. Constructor signatures describe the fields.
- Choose one canonical representation of strings, normally `Seq Char`, and one
  canonical interpretation of each extension application.
- Represent numeric parameters structurally. Separate their syntactic shape
  from semantic validity, such as a positive BV width or a valid field modulus.
- Include floating-point formats and rounding modes in the migration inventory.
  They may initially remain opaque extensions, but must retain distinct identity.

Provide a central executable sort-validation predicate, parameterized by a
checked declaration/extension signature. A raw syntax constructor may exist for
malformed input; no checked expression or theory route should treat that input
as a valid interpreted sort.

### 2.2 Extension mechanism

An extension application is data, not a function closure embedded in the AST.
Its signature specifies parameter shapes, arities, identities, and the operators
owned by that extension.

Distinguish two capabilities:

1. **Opaque support:** a nonempty model carrier and generic SMT operations such
   as equality, `ite`, and quantification; no extension-specific rewrite laws.
2. **Interpreted support:** validated parameters, semantic operations, and
   verified laws connecting recognized syntax to the shared model.

Unknown operators may remain uninterpreted where the checker contract permits
that abstraction. A theory-specific proof step must not be certified using laws
for an unsupported extension. Preserve the existing partial/rejection protocol.

Extension contracts must have a constructible witness and compose with the
other contracts used by the same checker theorem. An uninstantiated assumption
of soundness is not a replacement for this obligation.

### 2.3 Expressions and function declarations

Retain `Var`, `App`, and `Quantifier`, including explicit lambda sorts. A new
intrinsically typed expression language is not required for this change.

Strengthen checked well-sortedness to include:

- Valid sorts and registered declaration identities.
- Argument/domain and result/range agreement.
- Scoped de Bruijn variables, using the existing `Z3Definitions.scoped` checks.
- Boolean bodies for universal/existential quantifiers.
- Nonempty, correctly ordered array domains for lambdas.
- Valid parameters and operator signatures for interpreted declarations.

Audit `func_decl.interp` and `int_params` alongside sort migration. The existing
integer tag can remain if it is a verified, collision-free normalization of
native family/kind identities. Otherwise introduce a structured operator key.
Add typed declaration parameters only where required by modeled operations;
do not mechanically duplicate every native AST metadata field.

### 2.4 Semantic carriers and equality

Use the sort-indexed value/argument/environment framework already present in
`Z3DatatypeValue`, `Z3SortedSemantics`, and `Z3TypedRoot`.

Keep three notions separate:

| Notion | Required property |
|---|---|
| Sort/expression identity | Executable structural equality |
| Semantic value equality | Propositional/extensional equality |
| Executable theory equality | An explicit decision procedure only for carriers that provide one |

The semantic model may use ghost equality and ghost functions. Extraction must
erase that specification machinery; the checker must validate certificates
without attempting to compare arbitrary array functions or arbitrary reals.

Preserve inhabited carriers. For arrays, state select/store, extensionality, and
lambda laws over the full declared index tuple and result carrier.

Datatype composition requires additional work. Replacing a carrier argument
with a recursive datatype value family is not automatically a valid F*
definition, especially when arrays introduce function domains. Validate datatype
well-foundedness/positivity and design the semantic construction explicitly.
Keep unsupported recursive combinations excluded until their model exists.

## 3. Phased implementation

The phase order reflects semantic prerequisites. Each phase should be a
reviewable change with its own focused regression cases.

### Phase 1: Establish representation contracts and migration fixtures

Inventory sort construction and matching across F* modules, both native bridges,
generated-code adapters, and native bridge tests. Distinguish standalone theory
models, production checker modules, and typed-root test modules.

Add focused fixtures for:

- Different native declarations with identical display names.
- Built-in-looking user sort names such as `Int`, `BV32`, and `SeqInt`.
- BV widths, field moduli, sequence bases, and datatype instantiations.
- Multi-index arrays versus nested arrays.
- Malformed parameters and unsupported extension applications.

Document import identity and well-sortedness obligations before changing their
representation. Freeze existing supported-case behavior as the migration
baseline; do not broaden acceptance in this phase.

Acceptance: each supported imported sort has an unambiguous canonical identity;
distinct valid native sorts are not accidentally identified.

### Phase 2: Introduce structured sorts and migrate both bridges

Change `Z3AstTheory.sort`, equality, validation, and the constructors used by
theory modules. Replace string-built BV/FF parameters and the sequence markers
with structural forms.

Migrate OCaml and Cherry importers together. Update `Z3Native.fsti`,
`Z3NativeProof.fst`, runtime adapters, and tests wherever their interfaces change.
Regenerate extracted sources through the existing build process rather than
editing generated representations by hand.

Keep named helper functions such as `bv_sort` where useful, but make them
construct structured syntax. Remove semantic dependence on parsing names.
Retain unrelated resource bounds; a width bound may still be necessary for a
particular executable algorithm even after string decoding disappears.

Acceptance: structural equality agrees with native identity for the supported
sort grammar; both backends agree on sort structure and support classification.

### Phase 3: Generalize array semantics and affected lemmas

Adapt typed-root carrier definitions to the new sort grammar. Reuse its ghost
function-space construction, tuple indices, classical update decision, and
extensionality proofs.

Audit value-side `eqtype` constraints in `Z3ArrayTheory`,
`Z3ArrayGroundIndexEq`, and related helpers. Generalize lemmas that only use
propositional equality to `Type`. Where executable list membership currently
requires decidable equality of value-containing pairs, use a propositional
membership specification or formulate the premise over keys instead.

Retain specialized executable helpers where useful; do not force arbitrary
semantic functions into an `eqtype` or encode them as integers.

Acceptance: the shared semantic laws cover array-valued elements, array-valued
indices, mixed Bool/Int/Real carriers, and multi-index domains within the
explicitly supported datatype-free fragment.

### Phase 4: Connect generalized arrays to the production proof route

Bridge generalized array laws to the existing sorted proof/document framework.
Replace dependence on the fixed `VArr : arr int int` domain in migrated
contracts and rule soundness proofs. Preserve legacy modules only where they
still serve non-migrated rules or standalone examples.

Widen array recognizers only after their soundness proofs use the generalized
model. Enforce supported-sort/schema/expression checks before certifying steps
that rely on those laws.

Include array-valued equality, `ite`, binders, lambdas, and extensionality
witnesses in the integration review; select/store alone is insufficient.

Acceptance: nested-array certificates are checked against the generalized
model, unsupported datatype combinations cannot enter that route, and existing
supported proofs retain their outcomes.

### Phase 5: Add compositional sequences and character semantics

Interpret `Seq s` over values of the element-sort carrier. Generalize basic
list operations such as concatenation, length, and extraction where equality is
not required. Separate equality-dependent operations from these generic laws.

Provide ghost equality-based specifications for semantic operations that compare
elements, while keeping executable specialization where an element decision
procedure is available. Cover sequences of arrays without requiring executable
equality on function values.

Introduce a bounded character carrier matching the native character theory.
Connect string literals, character conversion, ordering, and string-specific
operations to it. Update regex sort matching to preserve the sequence basis.
Correct stale 8-bit-character comments.

Acceptance: integer sequences, strings, and sequences of arrays have distinct,
correctly composed semantics; string rules cannot be applied to arbitrary
integer sequences.

### Phase 6: Complete datatype and remaining extension composition

Extend checked datatype signatures with explicit declaration identities and
instantiations. Establish a semantic construction for the admitted recursive
fragment, then handle datatype fields containing arrays/sequences and arrays
whose index or element sorts are datatypes.

Add interpreted extension instances incrementally: BV, finite fields, finite
sets, and other families required by checker rules. For finite sets, include a
finite-support invariant and cardinality laws; arbitrary predicates alone do
not establish finiteness.

Each instance must preserve parameter identity, inhabitance, operation typing,
and coexistence with the already interpreted theories. Keep remaining families
opaque and report their proof-rule limitations explicitly.

Acceptance: each newly advertised composition has a constructible shared model,
verified rule laws, and end-to-end coverage. Do not claim unrestricted recursive
datatype composition from tests of only flat constructors.

## 4. Verification and regression strategy

### Proof obligations

- Prove sort equality correct with respect to the new syntax.
- Establish well-sortedness preservation for substitution, lifting, rewriting,
  instantiation, and lambda construction after the sort changes.
- Preserve scoped binder typing and tuple-coordinate order.
- Prove each migrated recognizer connects to the corresponding semantic law.
- Exhibit one model satisfying the composed contracts, rather than proving
  rule correctness only under potentially inconsistent assumptions.
- Ensure model definitions and semantic equality remain ghost/non-extracted.

### Focused semantic cases

| Area | Positive case | Negative or boundary case |
|---|---|---|
| Sort identity | Same declaration imports consistently | Same spelling does not merge distinct declarations |
| Parameterization | BV8/BV32, FF5/FF7, Seq Int/Seq Bool remain distinct | Invalid widths/moduli fail validation |
| Nested arrays | Read back a stored inner array and its stored real value | Wrong inner value does not verify |
| Array indices | Extensionally equal array indices select the same value | Distinct array indices preserve the other location |
| Multi-index arrays | Update/read a heterogeneous tuple | Coordinate order and tuple arity are not interchangeable |
| Lambdas | Beta and extensionality at nested array sorts | Ill-sorted bodies and empty binder domains are rejected |
| Sequences | Generic laws over array elements | Integer-sequence rules do not imply character range laws |
| Datatypes | Different instantiations retain their signatures | Unsupported recursive combinations stay unsupported |
| Finite sets | Finite support and cardinality compose with element sorts | Infinite predicates are not admitted as finite sets |
| Extraction | Both native backends check the same supported inputs | Unsupported theory steps are not reported as certified |

Reuse `Z3TypedRootTests.fst`'s existing nested and multi-index examples. Extend
existing test modules where practical; introduce a new module only for a
distinct obligation that does not fit an existing owner.

### Harness and scope

Use the existing verification/extraction harness and its dependency-ordered
`tools\checker_modules.json`. Register production dependencies as production
modules only when the production route actually uses them. Retain focused
proof regressions in the test list.

From the repository root, the existing full OCaml/native validation entry is:

```powershell
.\fstar\tools\build_ocaml_checker.ps1 -RunTests
```

For Cherry coverage, add the documented `-BuildCherry` and
`-CherryFstarExe` options with the configured Linux/WSL toolchain. The harness
builds and installs checkout Z3, selects it for F* verification, and links the
native checker against that installation.

During development, use the harness's dependency-scope facilities and focused
tests for each phase. Before promoting a new production route, run the full
registered scope and both native backends. Record support and acceptance
changes separately from compilation success.

Bound structural sort/parameter traversal at native input boundaries just as
expression traversal is bounded. Preserve DAG sharing where practical; changing
strings to recursive sort syntax must not introduce uncontrolled expansion.

## 5. Completion criteria and non-goals

The migration is complete for an advertised fragment when:

1. Imported sorts preserve declaration identity and interpreted parameters.
2. Checked expressions enforce the strengthened sort and signature invariants.
3. Supported nested combinations have compositional, inhabited carriers.
4. Array and sequence semantics do not require a blanket semantic `eqtype`.
5. Migrated rule proofs use the same constructible shared model.
6. OCaml and Cherry routes enforce support checks and agree on outcomes.
7. Unsupported extensions remain explicitly opaque, partial, or rejected.

This plan does not require mirroring native reference counts, hash-consing, or
all declaration metadata. It does not require runtime evaluation of arbitrary
semantic equality, a rewrite of the expression language, or immediate support
for every native theory. Its objective is a faithful, extensible representation
whose advertised semantic coverage is both verified and enforced.
