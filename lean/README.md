# Lean proof workspace

This workspace pins **Lean 4.34.0** and supports the
[proof integration plan](../doc/lean-proof-plan.md). A first native-certificate
reconstructor now handles `asserted` and `unit-resolution` Boolean proofs.
Other native proof rules are still unsupported.

## Check a native Z3 refutation

From the repository root:

```sh
PYTHONPATH=build/python python3 examples/python/proof_certificate.py \
  lean/examples/unit_resolution.smt2 > /tmp/unit_resolution.json
PYTHONPATH=build/python python3 examples/python/proof_to_lean.py \
  lean/examples/unit_resolution.smt2 /tmp/unit_resolution.json \
  -o /tmp/unit_resolution.lean
```

The second command checks the generated proof with Lean before publishing it.
It requires the original input separately and verifies that the certificate's
assertion roots match that input. Unsupported rules and invalid certificates fail
explicitly; the producer's `unsat` label is never enough.

The generated theorem derives `False` from the encoded original assertions using
Lean core proof terms, without new axioms or `sorry`. Parsing and SMT-to-Lean
statement translation remain trusted frontend components. See
[the exporter documentation](../examples/python/README) for the exact scope and
trust boundary.

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