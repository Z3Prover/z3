# SQL equivalence in F*

## Result

The original five `Sql.*.fst` modules formalize a pure, terminating SQL query model.
**All five modules verify in F* 2026.09.27 with checkout Z3 5.3.2 and 5.3.4.**
The study contains **22 query-equivalence problems: 10 proven equivalent
and 12 refuted by mechanically checked, concrete counterexamples**.
Six problems are derived from five BIRD Mini-Dev questions; five are
derived from four Spider reference-query patterns; eleven are additional
relational/SQL rewrite problems.

The equivalent cases are universally quantified over arbitrary finite
input tables, not established by testing a particular database.
The negative cases compute both results in F* and exhibit an output row
with different multiplicities. The three BIRD negative cases additionally
prove the explicit negation of universal `equivalent`.
No module uses an admission, added axiom, lax verification, or disabled
verification. The maximum explicit SMT resource limit is 10.

These are **authored equivalence problems based on published SQL queries**,
not official BIRD/Spider equivalence labels or a measured accuracy score.
BIRD and Spider provide text-to-SQL examples, not a catalog of proven
equivalence pairs. A negative result refutes our proposed rewrite, not the
dataset's reference query.

The later [Cherry SQL optimizer and solver](sql_solver/README.md) extend
this foundation with an executable, verified optimization repertoire and
Z3 user-propagator saturation. See the final section of this report for
its architecture, validation, and local executable artifacts.

## Files and reproduction

| File | Purpose |
|---|---|
| `Sql.Core.fst` | Values, three-valued predicates, bags, relational operators, grouping, aggregates, sorting, subquery primitives |
| `Sql.Query.fst` | Compositional query syntax, explicit database/outer-row environments, total interpreter |
| `Sql.Laws.fst` | Reusable induction proofs and lifting/witness lemmas |
| `Sql.Examples.fst` | Ten universal equivalence proofs and twelve counterexample certificates |
| `Sql.Tests.fst` | Six groups of normalization-checked semantic regressions |
| `tools\verify_sql.ps1` | Dependency-ordered, fail-fast verification and SQLite regression runner |
| `tools\test_sql_semantics.py` | Offline, standard-library-only SQLite checks; exact SQL pairs, schemas, data, expected results |

From the repository root, with an installed F*:

```powershell
.\fstar\tools\verify_sql.ps1 -FstarExe C:\fstar\fstar\bin\fstar.exe -Refresh
```

The default backend is `build\z3.exe`; override it with `-Z3Exe`.
The runner reads its version and supplies both `--smt` and `--z3version`,
without bypassing the version check. Generated caches default to
`build\fstar-sql-cache`. `-CacheDir` selects another cache; a new directory
gives a fresh-cache run. Standard-library caches are reused, but the
five project modules are checked in dependency order. Strict dependency
warning 241 is enabled. No native Z3 checker, OCaml extraction, full Z3
rebuild, or download of dataset databases is needed for this formalization.

To run only the independent SQL tests:

```powershell
python .\fstar\tools\test_sql_semantics.py
```

Validation performed on 2026-11-05:

- Fresh-cache verification of all five modules, with `--z3refresh`:
  every verification condition discharged successfully.
- F* version `2026.09.27`, commit
  `7deb38a27c86990664c6b41e4b6093597acdebd4`.
- SMT backend `build\z3.exe`, version `5.3.2`, build hash
  `aa71a62fdffbfede37f7558b52da4d52841e04ea`.
- SQLite `3.50.4`: all three test methods passed. They exercise ten
  equivalent pairs on 100 deterministic generated databases each
  (including empty tables, duplicates, NULLs, and boundary values),
  twelve separating databases, and nine additional SQL edge checks.
- Fixture primary/foreign-key constraints are enabled and checked.
- Solver stdin/model and help smoke tests passed. Python binding smoke
  testing passed with `builtins.Z3_LIB_DIRS` explicitly selecting `build`;
  the initial default DLL search found an incompatible pre-existing DLL.
  No unrelated build artifact was changed to address that search issue.

Before publication on 2026-11-06, `cmake --build build --target shell test-z3
--parallel 16` and `build\test-z3.exe /a` both passed. All five F* modules
were reverified with `--z3refresh` against rebuilt Z3 `5.3.4`, build hash
`7fb2231271869cda03008f491526f2d57d079517`; the SQLite regressions and
solver/help/Python binding smoke tests also passed again.

The Python checks are independent executions of the SQL pairs, **not an
extraction or execution of the F* interpreter**. The F* computations are
checked by `assert_norm`. The SQL-to-F* correspondence is a documented,
manual translation, not a certified parser/compiler.

## Semantics and equivalence

### Values, bags, and NULL

`Number n d`, with positive `d`, denotes the exact rational `n/d`.
`Null` and `Text s` complete the value domain. Numeric equality compares
cross products, so `Number 1 2` and `Number 2 4` denote the same value.
Rows are finite value lists; relations are finite row lists whose
repeated elements preserve SQL multiplicity.

Two notions of equality must not be confused:

- `sql_eq Null Null = Unknown`. WHERE, ON, HAVING, and CASE WHEN accept
  only `Yes`; both `No` and `Unknown` fail the condition.
- `same_value Null Null = true`. DISTINCT, grouping, set operations,
  and result comparison use this NULL-identifying equality.

`sql_and`, `sql_or`, and `sql_not` implement SQL's three-valued truth
tables. Consequently, excluded middle is not an allowed simplification
for nullable predicates, and NOT IN is not generally NOT EXISTS.

For unordered results:

```text
bag_equal a b =
  forall row. multiplicity row a = multiplicity row b

equivalent left right =
  forall database. bag_equal (left database) (right database)
```

`equivalent_under` adds an explicit database invariant, allowing future
proofs to require keys, foreign keys, non-nullability, or other integrity
constraints without silently assuming them.

Ordered comparison is pointwise `same_row` comparison of sequences;
`query_ordered_equivalent` uses it. Exact list equality, used in several
proofs, is an even stronger sufficient certificate. UNION ALL
commutativity is deliberately proved only for bags, not sequences.

### Supported query operations

| Feature | Representation and behavior |
|---|---|
| SELECT, aliases, derived tables | Projection functions and nested query nodes; aliases are resolved to positional columns |
| WHERE, AND/OR/NOT | Three-valued row predicates and `Where` |
| Arithmetic/comparisons | Exact rational `+`, `-`, `*`, `/`, equality/order, BETWEEN |
| CASE, COALESCE, NULLIF, IS NULL | Pure value/predicate combinators |
| LIKE | Case-sensitive character matching with literal tokens, `_`, `%`; escaped literals are elaborated into `LiteralChar` |
| DISTINCT | Duplicate elimination using NULL-identifying row equality |
| INNER/CROSS JOIN | Nested-loop bag join; CROSS JOIN uses an always-true condition |
| LEFT JOIN | Null extension of unmatched left rows, with an explicit right-side width |
| GROUP BY | One group per distinct key tuple, with NULLs grouped together |
| HAVING | `Where` over the rows emitted by `GroupBy` or `Aggregate` |
| COUNT(*), COUNT(expr) | Row count versus non-NULL expression count |
| SUM, AVG, MIN, MAX | Ignore NULL operands; empty/all-NULL input gives NULL except COUNT gives zero |
| Aggregate DISTINCT | DISTINCT flag on COUNT/SUM/AVG; MIN/MAX are already duplicate-insensitive |
| UNION/INTERSECT/EXCEPT | Both set and ALL multiplicity-sensitive forms |
| EXISTS, IN, NOT IN | Subquery result primitives and query-condition constructors; duplicates do not multiply EXISTS results |
| Correlation | Explicit outer-row environment; nearest enclosing row is available via `outer_col` |
| Scalar subquery | Empty result is `Some Null`; one scalar is `Some v`; wrong shape/cardinality is `None` |
| ORDER BY | Lexicographic keys, independent directions and NULL placement, stable tie handling |
| LIMIT/OFFSET | `Slice`, or `take` after `drop` |
| Nonrecursive CTE | F* let-bound query plans reused by name; no dedicated CTE node is required |

A no-GROUP-BY aggregate emits one row even on empty input. An ordinary
GROUP BY emits no groups on empty input. `Aggregate` is the appropriate
representation for the empty grouping set; `GroupBy []` must not be
used to model SQL `GROUP BY ()` on empty input.

The query syntax is an **elaborated, higher-order relational language**:
scalar and predicate fields are total F* functions, not raw SQL strings.
They can compose the primitive semantics or close over a subquery.
This keeps user-defined expressions and proof statements extensible,
while requiring the user to select SQL-correct functions. For scalar
subqueries, callers must handle `None` or prove singleton cardinality;
silently converting multiple rows to NULL is not licensed.

### Reusable proofs

`Sql.Laws` proves selection fusion, commutation, idempotence, distribution
over UNION ALL, projection composition/distribution, correct selection
pushdown through projection by substitution, multiplicity additivity,
bag commutativity of UNION ALL, NULL-aware COUNT rewrites, conditional
COUNT, and WHERE-to-INNER-JOIN-ON movement. The selection and join results
are structural inductions over arbitrary input tables.

`lemma_query_where_fusion` lifts selection fusion to the query interpreter
for arbitrary databases, outer rows, conditions, and input query plans.
`lemma_not_equivalent` turns a multiplicity witness into the negation of
universal database equivalence.

## Dataset provenance

**BIRD Mini-Dev:** BIRD SQL team, canonical
[birdsql/bird_mini_dev](https://huggingface.co/datasets/birdsql/bird_mini_dev),
revision `5b256b5a9c17478f06ed6912612e9a14d17065c8`,
[SQLite annotations](https://huggingface.co/datasets/birdsql/bird_mini_dev/blob/5b256b5a9c17478f06ed6912612e9a14d17065c8/data/mini_dev_sqlite.jsonl).
This is the October 2026 update. Question IDs in this report refer to
that pinned file, not to an older Mini-Dev release. Its query excerpts
and adaptations retain attribution and are shared under
[CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/).
Changes include aliases, predicate movement, and intentionally invalid
candidate rewrites, explicitly identified below. No database contents,
questions, or large dataset copy are checked into this repository.

| BIRD question_id | Database | Reference-query operation | Problems |
|---|---|---|---|
| 9 | california_schools | Return every NCES identifier tied for maximum enrollment among three CDS codes | N01 |
| 49 | card_games | Borderless card IDs with a missing Card Kingdom identifier, ordered by ID | E02 |
| 55 | card_games | COUNT(DISTINCT card ID) over banned legalities of white-bordered cards | E03, N02 |
| 297 | student_club | Income notes filtered by source and receipt date | E01 |
| 346 | superhero | Count neither-good-nor-bad superheroes through a LEFT JOIN to alignment | N03 |

**Spider:** Tao Yu et al., *Spider: A Large-Scale Human-Labeled Dataset
for Complex and Cross-Domain Semantic Parsing and Text-to-SQL Task*
(2018), [repository](https://github.com/taoyds/spider),
revision `b7b5b8c890cd30e35427348bb9eb8c6d1350ca7c`,
[gold_example.txt](https://github.com/taoyds/spider/blob/b7b5b8c890cd30e35427348bb9eb8c6d1350ca7c/evaluation_examples/gold_example.txt),
Apache-2.0. All selected Spider queries use `concert_singer`: source
lines 1 (COUNT), 9 (DISTINCT country), 15 (capacity BETWEEN), and
29 (stadium NOT IN concert). E06 additionally uses that schema but is
an authored NULL-aware COUNT example, not another gold-query claim.

**Elsewhere:** E06-E10 and N07-N12 are authored SQL/algebra examples.
Their semantics follow the SQL constructs documented, for example, in
PostgreSQL's [aggregate functions](https://www.postgresql.org/docs/18/functions-aggregate.html),
[subquery expressions](https://www.postgresql.org/docs/18/functions-subquery.html),
and [table expressions](https://www.postgresql.org/docs/18/queries-table-expressions.html).
They are not attributed to an external benchmark corpus.

The exact executable SQL pairs are retained in `EQUIVALENCES` and
`COUNTEREXAMPLES` in `tools\test_sql_semantics.py`. Fixtures are small
synthetic databases over the referenced columns, not records taken from
the benchmark databases.

## Equivalent query pairs

Every theorem below is parameterized by an arbitrary `database`.
E07/E08 also quantify over arbitrary three-valued predicates; E10
quantifies over arbitrary total projections.

| ID / F* lemma | Source | Left versus right | Why valid |
|---|---|---|---|
| E01 `e01_bird297` | BIRD 297 | Combined source/date WHERE versus two nested WHEREs | A conjunction passes exactly when both conditions pass |
| E02 `e02_bird49` | BIRD 49 | Combined borderless/missing-ID WHERE versus nested filters, retaining SELECT and ORDER BY | Selection fusion; exact ordered output equality is proved |
| E03 `e03_bird55` | BIRD 55 | WHERE status='Banned' AND borderColor='white' versus placing those conditions in INNER JOIN ON | Identical joined bag, hence identical COUNT(DISTINCT id) |
| E04 `e04_spider_count_one` | Spider line 1 | COUNT(*) versus COUNT(1) | Constant 1 is never NULL, including on empty input |
| E05 `e05_spider_between` | Spider line 15 | capacity BETWEEN 5000 AND 10000 versus 5000 <= capacity AND capacity <= 10000 | Inclusive bounds, with the same NULL behavior |
| E06 `e06_nullable_count` | Authored / Spider schema | COUNT(age) versus COUNT(*) after WHERE age IS NOT NULL | Both count exactly the non-NULL operands |
| E07 `e07_count_case` | Authored | COUNT(CASE WHEN p THEN 1 END) versus COUNT(*) after WHERE p | False and unknown conditions produce NULL operands |
| E08 `e08_union_all_filter` | Authored | Filter after UNION ALL versus UNION ALL of filtered inputs | Selection distributes without discarding multiplicities |
| E09 `e09_union_all_commute` | Authored | A UNION ALL B versus B UNION ALL A | Multiplicities add commutatively; order is not preserved |
| E10 `e10_projection_pushdown` | Authored | Filter p after projection f versus project f after filtering by p(f(row)) | Correct expression substitution, not blind column reuse |

For example, the actual BIRD 55 reference operation is:

```sql
SELECT COUNT(DISTINCT c.id)
FROM cards AS c JOIN legalities AS l ON l.uuid = c.uuid
WHERE l.status = 'Banned' AND c.borderColor = 'white'
```

E03 preserves the entire joined bag before aggregation. No uniqueness or
non-nullability assumption is needed for the law. This is stronger than
testing that two aggregate values happen to agree on existing card data.

## Non-equivalent pairs and separating databases

Brackets below denote result bags. Repeated rows remain repeated.
The SQL fixtures include all data needed to reproduce both sides.

| ID / F* lemma | Source / invalid rewrite | Separating database | Left output | Right output |
|---|---|---|---|---|
| N01 `n01_bird9` | BIRD 9: all maxima -> ORDER BY enrollment DESC, CDSCode DESC LIMIT 1 | Codes 1751010130583 and 1612910137588 have equal enrollment 100, identifiers 00001 and 00002 | `[00001,00002]` | `[00001]` |
| N02 `n02_bird55` | BIRD 55: COUNT(DISTINCT id) -> COUNT(id) | One white card; two banned legality rows, in different formats | `[1]` | `[2]` |
| N03 `n03_bird346` | BIRD 346: LEFT JOIN -> INNER JOIN | One superhero with NULL alignment_id; empty alignment table | `[1]` | `[0]` |
| N04 `n04_spider_count_age` | Spider COUNT: COUNT(*) -> COUNT(age) | One singer with NULL age | `[1]` | `[0]` |
| N05 `n05_spider_not_in` | Spider line 29: NOT IN -> correlated NOT EXISTS | Stadium `(1,A)`; one concert with NULL stadium_id | `[]` | `[A]` |
| N06 `n06_spider_distinct` | Spider line 9: delete DISTINCT | Two singers older than 20, both from France | `[France]` | `[France,France]` |
| N07 `n07_sum_empty` | SUM(x) -> COALESCE(SUM(x),0) | Empty numeric table | `[NULL]` | `[0]` |
| N08 `n08_average_null` | AVG(x) -> SUM(x)/COUNT(*) | Values 2 and NULL | `[2]` | `[1]` |
| N09 `n09_average_of_averages` | Overall AVG -> unweighted AVG of group AVGs | Group 0: 2,4; group 1: 12 | `[6]` | `[7.5]` |
| N10 `n10_union` | UNION ALL -> UNION | Each operand yields 1 | `[1,1]` | `[1]` |
| N11 `n11_outer_predicate` | LEFT JOIN: move WHERE right.x>0 into ON | Left `(1)`; empty right table | `[]` | `[(1,NULL,NULL)]` |
| N12 `n12_order_limit` | Reverse ORDER BY direction under LIMIT 1 | Values 2 and 1 | `[2]` | `[1]` |

N01's tie-breaker makes the candidate deterministic; it still loses a
required tied row. This is not a complaint about a particular engine's
choice among ties. Numeric CDS codes in F* stand for the successful
CASTs in this concrete fixture, not a general formalization of SQLite
CAST. N02 uses distinct `(uuid,format)` keys, not illegally duplicated
primary-key rows. N03 and N05 use nullable foreign keys; these witnesses
do not apply to a schema that forbids those NULLs.

N08's SQLite candidate explicitly uses `1.0*SUM(x)/COUNT(*)` to avoid
conflating its error with integer division. N09 uses exact rational
values in F*; the shown decimal 7.5 is exactly 15/2. N12 compares two
explicitly ordered queries, rather than assigning a fixed SQL meaning
to an unspecified LIMIT without ORDER BY.

## Translation layouts and assumptions

`database` maps numeric table identifiers to finite row bags. Unused
columns are projected away before translation:

| Problem | Table 0 row | Table 1 row |
|---|---|---|
| E01 | income `[notes; source; date_received]` | unused |
| E02 | cards `[id; borderColor; cardKingdomId; cardKingdomFoilId]` | unused |
| E03 / N02 | cards `[id; uuid; borderColor]` | legalities `[uuid; status; format]` |
| N01 | schools `[CDSCode; NCESSchool]` | frpm `[CDSCode; enrollment]` |
| N03 | superhero `[id; alignment_id]` | alignment `[id; alignment]` |
| E04/E06/N04/N06 | singer `[name; country; age]` | unused |
| E05 | stadium `[location; name; capacity]` | unused |

N05 uses a local stadium relation `[stadium_id; name]` and a projected
concert relation `[stadium_id]`. N07/N08/N12 use one-column numeric rows;
N09 uses `[group_key; value]`. N11's right width is explicitly two.

SQL queries are assumed to be statically well-typed and row widths
consistent with these layouts. The universal relational lemmas need no
schema constraints; interpreting them as the listed SQL pairs requires
this ordinary elaboration invariant.

## Limits and interpretation of the results

This is a foundation for SQL equivalence proofs, not a complete SQL
standard implementation or an automatic decision procedure.

- Exact rational arithmetic abstracts away floating-point rounding,
  fixed-precision DECIMAL rounding, integer overflow, and engine-specific
  integer division. Algebraic proofs must not be transferred to those
  domains without additional justification.
- Division by zero returns NULL, matching these SQLite examples; some
  SQL engines raise an error instead. Dynamic type errors are not modeled.
  Out-of-range columns return NULL as a totalization, not as SQL name
  resolution semantics. Ill-typed plans are outside the SQL interpretation.
- Text equality is exact; ordering uses F* string comparison. Collations,
  Unicode normalization, SQLite's default ASCII case-insensitive LIKE,
  implicit casts, dates/time zones, locale rules, and nonnumeric AVG
  coercions are not modeled. LIKE patterns have already been tokenized;
  SQL string-literal parsing and ESCAPE validation are outside this model.
- Scalar-subquery cardinality errors are represented by `None`; there
  is no whole-query exception semantics. Only the nearest correlated
  outer row is explicitly represented, not a general SQL scope stack.
- RIGHT/FULL joins, windows/OVER, recursive CTEs, grouping sets/ROLLUP,
  lateral queries, DML, transactions, JSON, nondeterministic functions,
  and vendor-specific scalar functions are outside the implemented fragment.
- Stable internal tie ordering is a chosen execution convention, not a
  SQL guarantee. Ordered equivalence claims require sufficient ORDER BY
  keys or must explicitly account for permitted tie permutations.
- No theorem asserts agreement of all supported plans with SQLite or
  PostgreSQL. F* proves properties of the authored semantics; regression
  tests provide finite evidence about the manual SQL translations.

The main findings are that NULL behavior, multiplicity, empty aggregates,
and tie preservation are essential proof obligations. INNER JOIN predicate
movement remains valid through aggregation, but an analogous LEFT JOIN
movement fails. COUNT and AVG rewrites require tracking which operands
are NULL; DISTINCT and UNION cannot be erased without constraints; and
top-1 selection is not a substitute for returning all extrema.

## Extension: proved optimizer repertoire and Cherry/Z3 solver

The optimizer adds `Sql.Optimize.fst`, `Sql.Native.fsti`, and
`Sql.Cherry.fst`. The updated PowerShell verifier checks all eight SQL
modules/interfaces. The original 22 equivalence-study results above
remain unchanged.

### Proof obligation and commercial optimizer transformations

The executable function `Sql.Optimize.rewrite` is accompanied by:

```text
forall interpretation, source.
  rewrite source = Some target
  ==> denote interpretation source = denote interpretation target
```

`denote` is defined using the existing SQL core: NULL-aware selection,
projection, bag union, joins, and aggregates. The theorem covers arbitrary
finite tables and arbitrary pure scalar/predicate interpretations.
It proves exact output-list equality, stronger than unordered bag equality.
No key, foreign-key, uniqueness, or non-NULL condition is silently assumed.

The catalogue has 27 tested concrete rule shapes:

| Family | Rules |
|---|---|
| Filter elimination | TRUE, FALSE, empty input, repeated identical filter |
| Predicate movement / view simplification | Fuse nested filters; push through projection with preimage substitution; distribute over UNION ALL; move WHERE into INNER JOIN ON |
| Projection simplification | Empty input, identity, compose nested projections, distribute over UNION ALL |
| UNION ALL simplification | Eliminate either empty operand; reassociate rightward |
| Join simplification | Empty left/right operands for CROSS and INNER JOIN; FALSE ON; TRUE ON to CROSS JOIN |
| Join distribution | CROSS/INNER JOIN distribute over a UNION ALL left operand |
| Aggregate normalization | COUNT(1) to COUNT(*); COUNT(expr) to filtered COUNT(*); COUNT(CASE WHEN p THEN 1 END) to filtered COUNT(*) |
| Partial aggregation | COUNT(A UNION ALL B) to addition of partial COUNTs |

These are relational specializations of optimization families used by
commercial databases. For example, Oracle documents view merging and
predicate pushing in its
[Query Transformations](https://docs.oracle.com/en/database/oracle/oracle-database/19/tgsql/query-transformations.html)
guide. This implementation supplies correctness transformations, not an
Oracle-compatible optimizer, cost model, or performance claim.
Bag-only join permutations and key-dependent elimination require further
proofs and metadata; they are not installed as arbitrary SMT equalities.

### SMT-LIB and user-propagator execution

`sql_solver\signature.smt2` gives the textual declarations for SQL query,
predicate, projection, and scalar constructors. Native `String` and `Int`
sorts carry names, constants, and column identifiers. The builder derives
the declaration table from this file. The frontend creates the functions
with `Z3_solver_propagate_declare` and preloads those exact declarations
into Z3's SMT-LIB parser.

The `created` callback discovers query terms; `eq` receives equality
events. The `final` callback traverses argument equivalence classes with
Z3's `congruence_root` and circular `congruence_next`. It considers
Cartesian combinations of argument representatives, including matches
that need more than one argument substitution. Candidates are decoded
and rewritten by the **actual Cherry-extracted F* function**.

An e-class match is propagated as
`(arg1=alternative1 AND ...) => source=target`.
Branch-local equalities are never used to justify unconditional rewrites.
User-propagator declarations suppress ordinary argument congruence, so the
callback also emits guarded functional-congruence equalities for all
registered constructors. This includes scalar and projection constructors,
and propagates inner query rewrites through their enclosing contexts.
After a successful propagation, the callback yields; Z3 internalizes new
terms/equalities and returns to final-check. Saturation finishes when no
additional enabled instance makes progress. Consequence caches are
cleared on pop and between checks. Matching/tree/instance resource
exhaustion returns UNKNOWN, including for cyclic e-classes.

This is an incomplete equational SQL solver. Asserting that two queries
are distinct and obtaining UNSAT proves their equality under the
constraints and the trusted implementation boundary. SAT is only a
model of instantiated rewrite equations, not an actual database witness.
The signature does not expose every operation in `Sql.Core`.
SQL text parsing, ordered/outer-join rewrites, general SUM/AVG pushdown,
and row-dependent scalar-theory reasoning remain outside this executable.

### Native build, package, and measured examples

The native build used WSL Linux x86-64, GCC/G++ 15.2.0, F* `v2026.10.25`
(commit `362e792b3aa882f1766b95c7450e3fe63081163d`), and a freshly built,
installed static checkout Z3 5.3.4. Every dependency was verified with
verification warnings treated as errors before Cherry extraction.
The kernel and runtime retain Cherry debug checks; C++ compilation uses
`-Wall -Wextra -Werror`. No lax checking or proof admission is used.

`tools\build_sql_solver.py` produces the native executable, metadata,
and a checksummed tar package containing the signature, documentation,
and Z3/F* licenses. Z3 is linked statically: `ldd` lists only standard
Linux runtime libraries, not libz3, F*, or OCaml.

Validation includes all 27 rule instances, multiple final-check rounds,
one- and multi-argument e-class matching, contextual congruence, push/pop,
native Int/String reasoning, non-theorems, malformed input, explicit budget exhaustion,
and genuinely cyclic e-classes. The packaged binary was extracted and
run with a clean environment. Archive checksum verification passed.

| Example | Result | Final callbacks | Accepted rewrites | E-class-dependent rewrites | Congruence steps |
|---|---|---:|---:|---:|---:|
| `aggregate.smt2` | UNSAT | 2 | 2 | 0 | 0 |
| `bird297.smt2` | UNSAT | 2 | 1 | 0 | 1 |
| `egraph.smt2` | UNSAT | 1 | 1 | 1 | 0 |
| `builtins.smt2` | UNSAT | 0 | 0 | 0 | 0 |
| `non-equivalent.smt2` | SAT, not a database witness | 1 | 0 | 0 | 0 |

The BIRD 297 example encodes E01's source/date filter fusion underneath
the original notes projection. It also checks that a successful inner
rewrite closes through an enclosing query constructor. Eleven native
test groups pass, including constructor congruence driven by arithmetic
equalities rather than only syntactically identical parameters.

The cyclic test `x = UNION ALL(x,a)`, at a ten-instance bound, returned
UNKNOWN after ten final callbacks, not a false SAT/saturation result.

Local persistent artifacts are:

```text
build\sql-solver\sql-solver
build\sql-solver\build.json
build\sql-solver\sql-solver-linux-x86_64.tar.gz
build\sql-solver\sql-solver-linux-x86_64.tar.gz.sha256
```

The binary is a Linux ELF executable, usable on this Windows machine
through WSL:

```powershell
wsl --exec bash -lc '/mnt/c/z3/build/sql-solver/sql-solver --stats /mnt/c/z3/fstar/sql_solver/examples/aggregate.smt2'
```

See `sql_solver\README.md` for the portable build and run commands.
The bridge's declaration/opcode fidelity, native AST marshalling,
callback integration, compiler/extraction toolchain, Cherry runtime,
and Z3 remain trusted. The F* theorem proves the optimizer's denotation
law, not the C++ marshaller or a certificate for the entire Z3 proof.
