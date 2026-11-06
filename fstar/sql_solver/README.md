# Cherry SQL rewrite solver

This is a native C/C++ executable containing a **Cherry-extracted F* rewrite
kernel**, the Cherry runtime, and **statically linked Z3**. It does not invoke
an external solver, F*, Python, or OCaml at runtime.

The solver reasons about relational plans, not raw `SELECT` text. It loads the
SMT-LIB signature in `signature.smt2` as user-propagator declarations. Input
files can use those symbols directly; do not redeclare the preloaded signature.
`--signature` prints the ordinary SMT-LIB declarations for external tools.
SQL syntax translation is manual.

## Running

Extract the binary package, then use Linux or WSL:

```sh
./sql-solver --stats example.smt2
./sql-solver --signature
./sql-solver --self-test
./sql-solver --max-steps 10000 --timeout 10000 example.smt2
```

With no file, or `-`, assertions are read from stdin. Inputs support the
SMT-LIB declaration/definition/assertion fragment and are checked once.
`check-sat`, push/pop command-stream execution, and model-printing commands
are not a CLI protocol. Incremental solver scopes are exercised by
`--self-test` using Z3's API. The parser environment is fresh per input parse.

Example, using Z3's built-in `String` and `Int` rather than custom encodings:

```smt2
(assert (distinct
  (sql.project (sql.one (sql.column (+ 1 1))) (sql.scan (str.++ "ord" "ers")))
  (sql.project (sql.one (sql.column 2)) (sql.scan "orders"))))
```

The answer is `unsat`. To prove two plans equal, assert their `distinct`
and check for UNSAT.

- **UNSAT:** the constraints are inconsistent with the proved rewrite
  equalities and Z3's theories, subject to the native bridge trust boundary.
- **SAT:** a model of the instantiated rewrite theory, **not a decoded database
  counterexample and not a proof of SQL non-equivalence**. The rule set is
  incomplete for SQL semantics.
- **UNKNOWN:** Z3 could not finish, or the rewrite/matching budget was reached.
  An incomplete saturation is never returned as SAT.

The five examples under `examples` cover aggregate rewriting, an e-class
alias, integer/string reasoning, the BIRD 297 income-query filter rewrite,
and a non-theorem. They are included in the binary package.
The BIRD-derived example retains its CC BY-SA 4.0 attribution in the file;
the original study's provenance is detailed in `FSTAR_SQL_REPORT.md`.

## Building from the repository

Requirements: Linux x86-64/AArch64 (WSL is supported), GCC/G++ 15+, CMake,
Ninja, Python 3, and a Cherry-capable F*. Tested with F* `v2026.10.25`,
commit `362e792b3aa882f1766b95c7450e3fe63081163d`.
The original PowerShell verifier also checks the optimizer with F*
`v2026.09.27`; that version is not used for Cherry extraction here.

From the repository root in Linux/WSL:

```sh
cmake -GNinja -S . -B build-sql \
  -DCMAKE_BUILD_TYPE=Release -DCMAKE_C_COMPILER=gcc-15 \
  -DCMAKE_CXX_COMPILER=g++-15 -DZ3_BUILD_LIBZ3_SHARED=OFF \
  -DZ3_BUILD_PYTHON_BINDINGS=OFF -DCMAKE_INSTALL_PREFIX="$PWD/build-sql/install"
cmake --build build-sql --parallel 16
cmake --install build-sql
python3 fstar/tools/build_sql_solver.py \
  --fstar /path/to/fstar/bin/fstar.exe \
  --z3-install build-sql/install --build-dir build-sql/sql-solver --run-tests
```

On Windows, run these Linux commands through `wsl --exec bash -lc '...'`;
the host PowerShell filesystem paths remain Windows paths.

The builder verifies every dependency before extracting
`Sql.Cherry.rewrite_native`. The generated C is compiled with Cherry debug
checks; the C++ frontend is compiled with `-Wall -Wextra -Werror`. Only the
extraction's monomorphic-ABI-name warning 377 is downgraded; verification
warnings remain fatal. Add `--sanitize` for AddressSanitizer/UBSan on the
kernel, runtime, and bridge. Z3 itself must be separately instrumented to
sanitize its internals.

Outputs are `sql-solver`, `build.json`, and a checksummed
`sql-solver-linux-ARCH.tar.gz` package with the signature and licenses.
The installed static Z3 and its headers must come from this checkout.
F* is explicitly given that installation's executable and actual version.

## Verified repertoire

`Sql.Optimize.rewrite` and `lemma_rewrite` implement/prove these families:

| Family | Transformations |
|---|---|
| Filter simplification | TRUE/FALSE/empty input; duplicate filter elimination |
| View/filter movement | Nested-filter fusion; push through projection with expression substitution; distribute over UNION ALL; move WHERE into INNER JOIN ON |
| Projection simplification | Empty input; identity; nested projection composition; distribute over UNION ALL |
| UNION ALL simplification | Empty operands; reassociate rightward |
| Join simplification | Empty operands; false join; true join to CROSS JOIN |
| Join distribution | INNER/CROSS JOIN distribute over a UNION ALL left operand |
| Aggregate normalization | COUNT(1) to COUNT(*); COUNT(expr) to COUNT(*) after non-NULL filtering; conditional COUNT to filtered COUNT(*) |
| Partial aggregation | COUNT(A UNION ALL B) to addition of partial counts |

These are correctness rules from the repertoire of relational optimizers,
not implementations of a vendor's optimizer or a claim that every rule is
always a cost improvement. View merging and predicate pushing are documented
commercial transformations, for example in
[Oracle's query transformations guide](https://docs.oracle.com/en/database/oracle/oracle-database/19/tgsql/query-transformations.html).
No cost model, index/access-path choice, physical join algorithm, or
cardinality estimator is included.

The theorem proves **exact relation-list equality** for arbitrary tables,
NULL-bearing predicates, projections, and scalar functions. All implemented
rules are therefore also valid bag equalities. Bag-only transformations
(UNION ALL commutation, join reordering without output-column repair, OR
expansion without overlap guards) are deliberately not imported as plan
equalities. LIMIT/ORDER BY, DISTINCT, outer joins, general SUM/AVG pushdown,
and key-dependent join elimination are not in this executable's signature.
Their presence in `Sql.Core` does not authorize applying unproved rules.
Scalar expression constructors such as `sql.add` and `sql.eq` are opaque
to this rewrite kernel. Z3 reasons natively about their `Int`/`String`
parameters; it does not thereby execute arbitrary row-dependent arithmetic.

## Final-check saturation and trust boundary

1. The builder derives the native declaration table from `signature.smt2`.
   The frontend creates the functions with `Z3_solver_propagate_declare`
   and passes those exact declarations to the SMT-LIB parser. There are no
   unregistered look-alike SQL functions.
2. `created` observes native query DAGs. `eq` receives equality events.
   The simple SMT solver is used; solver cloning/parallel contexts are not
   supported.
3. User-propagator declarations suppress Z3's automatic argument
   congruence. `final` explicitly propagates guarded functional-congruence
   equalities for all registered constructors, including scalar and
   projection constructors. This closes rewrites under enclosing queries.
   It then scans the observed query roots and visits each argument's e-class with
   `congruence_root` and circular `congruence_next`, exposes candidate shapes,
   and calls the extracted F* kernel. Cartesian combinations of argument
   alternatives are considered: matches must not depend on accidentally
   choosing matching representatives for only one argument.
4. A syntactic rewrite emits `source = target`. An e-class match emits the
   **guarded** theorem
   `(arg1 = alternative1 AND ...) => source = target`, not an unconditional equality.
   Thus a branch-local match cannot escape its hypothesis.
5. After an accepted propagation, `final` yields to Z3. Z3 processes new
   terms/equalities and calls `final` again. It finishes only when no
   additional enabled rule instance makes progress. The consequence cache
   is cleared on pop and before each check, because Z3 may discard scoped
   consequences. Observed syntax remains pinned.
6. Cyclic e-classes can generate an unbounded equational closure. Resource
   bounds stop such searches with UNKNOWN, not a false claim of saturation.
   Default bounds are 10,000 emitted instances/e-class visits/candidate matches, 8,192
   tree visits per native decoding, and a decoding depth of 32. Subtrees
   beyond the decoding depth are retained as opaque native atoms, not
   replaced by empty queries.

The verified theorem is about `Sql.Optimize.plan` interpreted with
`Sql.Core` operations. The C++ bridge's opcode/child lookup, atom identity,
native construction, SMT declaration typing, parser, Z3 callback protocol,
F* extraction, Cherry runtime, compilers, and Z3 remain trusted. The
foreign interface makes no axiomatic claims that arbitrary native terms
are equivalent. Its inspection/encoding correctness has not itself been
formally proved. No standalone F* certificate of the entire Z3 UNSAT
derivation is produced.

Runtime tests cover all 27 concrete rule shapes, multiple-round saturation,
e-class-dependent matches, contextual and functional congruence, theory interaction, non-theorems, malformed
inputs, explicit resource exhaustion, and push/pop backtracking.
