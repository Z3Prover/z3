# AST argument-order linter

`z3-ast-argument-order` warns when separate call arguments may allocate AST nodes:

```cpp
m.mk_and(a.mk_le(x, zero), a.mk_le(y, zero));
```

C++ leaves their relative evaluation order unspecified, which can change AST IDs
and solver behavior across compilers. Construct the arguments in separate statements
to make the order explicit. Warnings are advisory; the linter never offers or applies
automatic fixes.

The check follows known allocator entry points and visible wrapper definitions.
It can miss indirect and out-of-line calls, and may warn about calls that only
allocate conditionally. Use `NOLINT(z3-ast-argument-order)` for justified exceptions.

## Run locally

Requires LLVM/Clang and clang-tidy **21.1.8**, matching development packages,
CMake 3.27 or newer, Ninja, and Python 3.

```sh
cmake -G Ninja -S scripts/clang-tidy -B build-tidy \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_C_COMPILER=clang-21 -DCMAKE_CXX_COMPILER=clang++-21 \
  -DLLVM_DIR=/usr/lib/llvm-21/lib/cmake/llvm \
  -DCLANG_TIDY=/usr/bin/clang-tidy-21
cmake --build build-tidy

cmake -G Ninja -S . -B build \
  -DCMAKE_CXX_COMPILER=clang++-21 \
  -DCMAKE_BUILD_TYPE=Debug -DCMAKE_EXPORT_COMPILE_COMMANDS=ON \
  -DZ3_INCLUDE_GIT_HASH=OFF -DZ3_INCLUDE_GIT_DESCRIBE=OFF \
  -DCMAKE_ADD_CUSTOM_COMMAND_DEPENDS_EXPLICIT_ONLY=ON
cmake --build build --target src/api/api_log_macros.h src/ast/pattern/database.h
python3 scripts/clang-tidy/run.py \
  --plugin build-tidy/Z3TidyModule.so --build build --source-root . --output ast-order-report
```

Preparation compiles the plugin and generates Z3 headers, without compiling Z3.
The runner writes per-file logs, `warnings.txt`, and `summary.json`, deduplicating
header diagnostics. Use `--jobs` for parallelism and `--filter` to select source paths.

## CI reports

`ast-order-warning-report.yml` checks changed sources and transitive header
dependents on PRs, using `clang-scan-deps` on both base and the PR merge result.
The base is the merge commit's first parent, the base branch tip at scan time,
not `pull_request.base.sha`, which is where the branch forked from the base.
Generated file changes are included. Build configuration or checker changes trigger
full scans; master and nightly/manual runs also scan everything. Scans use all CPUs
and cache completed reports. Compiler or scanner failures fail the job.

`ast-order-warning-comment.yml` updates one PR comment with counts, the checked
scope, and a collapsed warning diff. Updates display **EDITED** with the UTC date
and time. Counts on PRs cover the affected files. Stale and incomplete comparisons
are rejected. The comment workflow runs trusted code from the default branch and
reads a bounded, validated report; it must be on that branch to post comments.
