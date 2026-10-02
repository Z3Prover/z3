# Lean proof workspace

This workspace pins **Lean 4.34.0** and supports the
[proof integration plan](../doc/lean-proof-plan.md). A first native-certificate
reconstructor now handles `asserted`, `unit-resolution`, `mp`, and Boolean
`rewrite`, plus `refl`, `symm`, `trans`, `trans*`, `iff-true`, `iff-false`,
Boolean `monotonicity`, `and-elim`, and `not-or-elim`, with scoped `hypothesis`
and `lemma` proofs and supported Boolean `def-axiom` clauses. Other native proof
rules are still unsupported.

## Check a native Z3 refutation

From the repository root:

```sh
PYTHONPATH=build/python python3 examples/python/proof_certificate.py \
  lean/examples/unit_resolution.smt2 > /tmp/unit_resolution.json
PYTHONPATH=build/python python3 examples/python/proof_to_lean.py \
  lean/examples/unit_resolution.smt2 /tmp/unit_resolution.json \
  -o /tmp/unit_resolution.lean
```

For an example that also requires implication rewriting and `mp`, replace
`unit_resolution` with `boolean_rewrite` in both commands. Use
`boolean_structural` to also exercise transitivity, congruence, and
negated-disjunction elimination. Use `boolean_branching` to exercise temporary
hypotheses and learned clauses. Use `boolean_def_axiom` for clauses forcing both
arguments of an xor to be true, requiring a Boolean gate clause after
preprocessing.

The second command checks the generated proof with Lean before publishing it.
It requires the original input separately and verifies that the certificate's
assertion roots match that input. Unsupported rules and invalid certificates fail
explicitly; the producer's `unsat` label is never enough.

The generated theorem derives `False` from the encoded original assertions using
Lean core proof terms, without any axioms or `sorry`. Boolean rewrites are checked
by exhaustive cases and kernel reduction, independently of the assertions.
Structural rules use direct logical proof terms, without truth tables.
Condensed transitivity (`trans*`) follows equivalence paths through its supplied
premises, including reversed and redundant edges, and composes the result with
`Iff.symm` and `Iff.trans`. It rejects disconnected endpoints and preserves the
hypothesis dependencies of every premise.
Each supported `def-axiom` clause is proved in a separate Lean theorem with no
input assertions, not introduced as an axiom. Gate clauses for not, and/or,
implication, equivalence, xor, and Boolean ite use direct proof terms over
immediate operands; nested atoms are not enumerated. Invalid or unsupported
clauses are rejected even when unused. Fresh-symbol definitions remain outside
this slice.
Open proof steps are functions of their temporary hypotheses. Each `lemma`
discharges all hypotheses of its contradiction, including in nested and shared
subproofs; a final proof with any open hypothesis is rejected.
Temporary decidability witnesses for rewrites, double-negation cancellation,
gate clauses, and learned clauses are eliminated constructively from the
refutation, so they do not become extra theorem hypotheses. Large rewrite truth
tables can exceed Lean's resource limits; failures never publish a proof.
Parsing and SMT-to-Lean statement translation remain trusted frontend components.
See [the exporter documentation](../examples/python/README) for the exact scope
and trust boundary.

## Audit preprocessing

The opt-in harness distinguishes real preprocessing from a pass skipped in
proof mode:

```sh
PYTHONPATH=build/python python3 examples/python/proof_preprocessing.py \
  lean/examples/boolean_solve_eqs.smt2 --require-search
```

It compares the simplifier and tactic APIs with proofs off/on and reports native
proofs, elimination/search statistics, and actual Lean replay results as JSON.
For a preprocessing-only contradiction, use `lean/examples/unit_resolution.smt2`
without `--require-search`. Refutations are checked against the original input,
not a replacement goal.

Both examples now succeed through both interfaces, with observed variable
elimination and Lean-checked, axiom-free refutations. The native producer
preserves equality-substitution evidence, including through incremental replay
and tracked assertions. `iff-true` and `iff-false` justify replacing Boolean
units by constants.

Proof mode supports direct equalities and Boolean units; theory-specific and
conditional extraction still await their own certificates and are skipped.
See [the plan](../doc/lean-proof-plan.md#preprocessing-evidence-audit) for the
boundary. The harness still rejects missing evidence and bypassed passes;
successful solver output alone does not count as verification.

## Recheck a proof artifact

`check_lean.sh` still accepts Lean source files, not JSON. To recheck the artifact:

```sh
./scripts/check_lean.sh /tmp/unit_resolution.lean
```

## Check proofs

From the repository root:

```sh
# Build and check the example library.
./scripts/check_lean.sh

# Check a file. The .txt extension is accepted as well as .lean.
./scripts/check_lean.sh /tmp/l.txt

# Check several files, stopping at the first failure.
./scripts/check_lean.sh path/to/first.lean path/to/second.lean
```

The script can be invoked from other directories too. Relative file arguments
are resolved against the caller's directory, not against the Lean workspace.
Paths containing spaces must be quoted. Use `--help` for usage.

The helper builds the local library before checking supplied files, so they can
use `import Z3Proofs`. It selects the toolchain from `lean-toolchain` explicitly,
independently of your default toolchain.

Checks use `--trust=0` to recheck imported modules and
`-DwarningAsError=true` to treat warnings, including ordinary `sorry`/`admit`
placeholders, as errors. A successful run prints `Lean checks passed.` and exits
with status 0; build or checking failures return a nonzero status.

This is a Lean source checker, not an audit of explicit axioms or other trusted
features, and not a sandbox for executing untrusted Lean code.

## Install the toolchain

Install [elan](https://github.com/leanprover/elan), the Lean version manager.
On macOS with Homebrew:

```sh
brew install elan-init
elan toolchain install "$(cat lean/lean-toolchain)"
```

The helper finds `elan` on `PATH`, or at `~/.elan/bin/elan` after a standard elan
installation. To make the pinned version your default outside this project:

```sh
elan default "$(cat lean/lean-toolchain)"
lean --version
```

No Mathlib or other external Lean packages are needed. Lake build artifacts
remain under the ignored `lean/.lake/` directory.

## Automated Lean proof checks

The Python script `scripts/proofs/proof_matrix.py` and its tests are in
[Z3Prover/z3test](https://github.com/Z3Prover/z3test/tree/master/scripts/proofs).
The CI job uses a separate `z3test-lean/` checkout at the fixed revision
specified in the workflow's "Check out Lean proof-checking tools" step.
This revision provides the required `--z3-source` and `--lean-artifacts`
options. Other Z3 tests use the independent `z3test/` checkout from its default
branch.

To run the same checks locally, use a z3test checkout at that revision, cloned
beside this Z3 checkout:

```sh
python3 ../z3test/scripts/proofs/proof_matrix.py \
  --z3 "$PWD/build/z3" --z3-source "$PWD" \
  --lean --cells legacy-proof-object --timeout 30 \
  --lean-artifacts /tmp/lean-proof-artifacts --out /tmp/lean-proof-matrix.jsonl \
  lean/examples/*.smt2
```

This requires a POSIX CMake build with the executable, shared library, and
Python bindings in `build/`. The producer uses those bindings to solve once;
the separate checking process consumes the saved native JSON and original input,
without solving again. Records identify the producer and retain input,
certificate, and checked Lean artifacts with their hashes.

Every input must have status `lean-verified` for success. Unsupported inputs,
sat/unknown, missing evidence, checking errors, and timeouts cause failure.
The `releaseClang` CI job runs the tests and checks all six Boolean examples
after installing Lean. It uploads the proof files even when a check fails.

The [planned additional test inputs](../doc/lean-proof-plan.md#additional-input-files-future-plan)
include seven examples from `jreeves3/SMT-Skeleton-Check` and the larger
collections named in its CSV result files. These are future additions, not
part of the six Boolean examples currently checked automatically.