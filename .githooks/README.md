# Git hooks

Versioned git hooks for this repository.

## pre-commit

Builds the `z3` binary and runs the [z3test](https://github.com/Z3Prover/z3test)
regression suite (`scripts/test_benchmarks.py` over `regressions/smt2`) locally.
The commit is aborted if the build or any regression fails.

### Enable

```bash
git config core.hooksPath .githooks
```

### Configuration (environment variables)

- `Z3_BUILD_DIR` — build directory to use/create (default: `build/release`).
- `Z3TEST_DIR` — existing `z3test` checkout. If unset, `z3test` is cloned into
  `../z3test-precommit` next to the repository.

### Skip for a single commit

```bash
git commit --no-verify
```
