# Checked Boolean/ITE reasoning and deep inputs: third v2 milestone

For the subsequent search improvements and current **355/390** checked coverage,
see [the fourth milestone](https://github.com/RSoulatIOHK/z3/blob/0a5210c9009ba5595521c39cefa7ef0a7b1d46aa/doc/QF_FF_PROOF_SEARCH.md). The results below record the
original Boolean/ITE milestone.

The standalone proof pipeline now handles general Boolean combinations of
prime-field equalities/disequalities and field-valued ITEs. It retains the
existing literal-conjunction path where applicable and automatically selects
the new `z3-ff-alethe-pac-v2` bundle profile otherwise. Normal Z3 solving and
native `get-proof` behavior are unchanged.

## Implementation and proof obligations

`scripts/ff_boolean_proof.py` supplies an iterative, typed, hash-consed term DAG.
Its explicit expansion frames preserve simultaneous `let` bindings, lexical
shadowing, declaration order, nullary definitions and sort ascriptions. The
parser accepts up to 100,000 nesting levels, with the existing file/token bounds;
expansion and retained DAG nodes have separate bounds. No increase to Python's
recursion limit is needed. Shared expressions become shared definitions in both
the polynomial inputs and Alethe, rather than exponentially duplicated trees.
The legacy checker's default 200-level parsing limit remains unchanged.

The supported Boolean operators are `not`, `and`, `or`, binary implication,
binary XOR, binary equality/equivalence and ITE, with `true`/`false` and Boolean
constants. Fields support constants, numerals, addition, multiplication,
negation and ITE. Fields remain prime and single-sort per bundle. Quantifiers,
nonconstant UFs, mixed fields, incremental scripts, other arithmetic theories,
`ff.bitsum` and other operators outside this explicit profile are rejected.

The producer constructs the Boolean connective truth-table clauses and searches
for a propositional assignment. For its assigned field literals it requests a
bounded Z3 polynomial refutation. Each successful refutation becomes a learned
field-conflict clause. Root-ancestor slicing removes unused input equations from
that lemma; its inverse witnesses remain tied to their original disequalities.
Identical derived clauses reuse their existing proofs, and only ancestors of
the final empty clause are exported. These are generic search/proof-sharing
choices; there are no artifact names or circuit-family special cases.

A field-valued ITE is represented by an opaque field variable during polynomial
reasoning. Its meaning is **not assumed**: Alethe `ite_intro`, equivalence,
resolution and conjunction projection establish the corresponding conditional
value equation. Ordinary Boolean ITE clauses then select its branch. Original
terms replace the opaque variables in the exported field lemma.

Each field contradiction is inside an Alethe subproof with explicit assumptions.
`ff_diseq`, polynomial normalization and `ff_poly_conversion` link those exact
assumptions to its PAC payload; `subproof` discharges them to a conflict clause.
The surrounding resolution proof must derive the empty clause from those
lemmas and clauses of the original formula. A field lemma alone cannot certify
the whole Boolean formula.

## Checking contract and files

The command remains:

```sh
python3 scripts/ff_proof_pipeline.py problem.smt2 --out /tmp/ff-proof \
  --z3 build-ff-cmake/z3 --carcara "$CARCARA" --ffpacheck "$FFPACHECK"
python3 scripts/ff_proof_pipeline.py --check --out /tmp/ff-proof \
  --carcara "$CARCARA" --ffpacheck "$FFPACHECK"
```

The new profile stores `boolean-certificate.json`, `proof.alethe`, the original
`problem.smt2`, and one polynomial input/PAC pair per field lemma. The JSON
contains field-literal lists with derivation DAGs and an explicit resolution
trace. Rechecking reconstructs input clauses independently, binds each lemma's
variables and modulus to the original field (including variable-free inputs),
replays its polynomial DAG, checks resolution pivots and backward references,
and requires an empty root clause. It then compares the exact stored Alethe and
PAC bytes and invokes the external checkers. The search procedure is never
rerun or trusted by the checker.

The pinned external checkers and the local FFPacheck completion patch are
unchanged from the previous milestone. The independent input binding remains
mandatory because of the documented Carcara PAC-premise gap. No holes or
admitted rules were introduced. A pure Boolean contradiction has no PAC lemma
and is checked directly by Carcara plus the independent Boolean verifier.

Bounds include 100,000 DAG nodes, 2M front-end operations, 10M Boolean search
work units, decision depth 256, 50,000 resolution records, 256 field lemmas,
4096 premises per field lemma, 32 MiB for exported Alethe/PAC/input data and a separate 32 MiB proof-ledger bound. Every field
lemma inherits the bounded scalar reconstructor and independent polynomial
checker limits. Exhaustion or an unavailable field certificate is **not SAT**.
There is no claim of complete QF_FF proof production or a process-wide memory cap.

## Regression evidence

The new suite accepts 30 end-to-end proofs through the external checkers and
rejects 22 deliberate corruptions or unsupported inputs. It covers Boolean
identities, field/Boolean/nested ITEs, field equalities as ITE conditions,
simultaneous and shadowed lets, nullary definitions, identifier collisions, and
primes 2, 3, 7 and a 254-bit prime. An 800-level let chain is checked externally;
12,000-level lets and 12,001 negations exercise the iterative front end.
A 400-level doubling DAG remains compact instead of expanding exponentially.

An exhaustive semantic oracle adjudicates 36 randomized mixed formulas over
F2/F3: 27 SAT inputs get no certificate, 7 UNSAT inputs are certified, and 2
UNSAT inputs explicitly remain unavailable. The oracle enumerates Boolean and
field assignments independently of the CNF and polynomial encoders.
The earlier 29 positive/25 rejection pipeline checks and the legacy 83
DAG/Alethe-pair suite (including 144 exhaustively adjudicated systems) pass.

Run the new suite with:

```sh
python3 z3test/regressions/finite_field/test_ff_boolean_proof.py --z3 build-ff-cmake/z3 \
  --carcara "$CARCARA" --ffpacheck "$FFPACHECK"
```

## Fixed-corpus screen

The benchmark runner is the same entry point and fixed selection: 408 member
paths, 390 distinct original inputs, four workers, and ten seconds total per
input, covering production, independent replay and external checking. All old
135 certified inputs remain certified. The final results below measure proof coverage, not a new CVC5 solver comparison.

| Outcome | Previous pipeline | This pipeline |
|---|---:|---:|
| Original-input proofs checked | 135 | **340** |
| Front-end profile rejection | 255 | **0** |
| Bounded polynomial reconstruction unavailable | 0 | **22** |
| Boolean search work limit | 0 | **28** |
| External checker rejection / timeout | 0 | **0** |

The gain is **205 additional certified inputs**, with no losses: 183 soundness
and 157 determinism inputs are now certified. The Boolean/deep profile supplies
1960 field lemmas across its 205 proofs; all are independently checked, checked
by FFPacheck, and composed by Carcara. The legacy path supplies another 135.

Median whole-pipeline time is **0.354 s**, maximum
**6.601 s**. The legacy 135-input path has median
**0.131 s**, compared with 0.128 s in the previous screen;
this small concurrent-run difference does not establish a performance change.
The new 205-input path has median **0.523 s**.
Median Alethe size is 163,122.5 bytes and maximum
is 7,004,018 bytes. These are four-worker screen
measurements, including subprocess supervision, not isolated solver timings.
No process-wide memory limit was applied.

The earlier ordinary Z3 result (382/390) is unchanged evidence from a separate
solver screen; the new 340/390 result counts complete checked proofs. It does
not establish superiority over CVC5's proof pipeline or the paper's different
403-input/1200-second evaluation.

Raw outcomes, original inputs, proof bundles and checker logs are archived in
`tests/finite_field/results/fmcad-proof-boolean-v2/`. A small Boolean/ITE bundle
is tracked under `z3test/regressions/finite_field/fixtures/certificates/artifact-boolean/`.

The next coverage bottlenecks are bounded Boolean search and polynomial proof
reconstruction. Root/field-completion evidence and theory-combination proofs
remain separate work; CPC/Lean reconstruction is still unimplemented.
