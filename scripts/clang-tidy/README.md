# Z3 determinism linter

One linter reports the determinism warnings below in a single pass. It runs
locally and in CI, reports warnings only, and never applies automatic fixes.

## AST argument order

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

## AST tuple destruction order

`z3-ast-tuple-order` warns about `std::tuple` with two or more elements that own
AST references, directly or through owning containers and by-value wrappers:

```cpp
std::tuple<func_decl_ref, expr_ref, expr_dependency_ref> definition;
```

libstdc++ and libc++ destroy tuple elements in different orders. Releasing AST
references in different orders can change recycled IDs and subsequent solver
behavior. Use a named struct, whose members are destroyed in reverse declaration
order. Numeric comparison tuples, raw pointers, and non-owning reference tuples
such as `std::tie` are accepted. Type aliases, deduced tuples, and tuple factories
are checked too.

The check recognizes Z3 AST reference types, standard owning containers and
visible wrapper fields/bases. It cannot infer ownership implemented only by
custom destructor code or hidden behind raw pointers. It skips expression checks
inside template instantiations to avoid reporting container internals, so some
dependent tuple constructions can be missed.
It warns conservatively without proving that references are the last owners.
Use `NOLINT(z3-ast-tuple-order)` for justified exceptions. No automatic fixes are offered.

## Random draw order

`z3-random-order` warns when separate arguments or operands may consume random
state in an unspecified order, for example:

```cpp
unsigned mask = (rng() << 16) | rng();
f(rand(), rand());
```

Draw the values in separate statements. The check recognizes C random functions,
Z3's `random_gen`, standard C++ random engines, and visible wrappers around them.
It respects C++17 sequencing, including braced initializers, shifts, short-circuit
operators and comma expressions. Like the AST check, it can miss indirect or
out-of-line wrappers. It conservatively warns even when calls use independent
generators or only draw conditionally; it does not prove that the generators alias.
Use `NOLINT(z3-random-order)` for justified exceptions. No automatic fixes are offered.

## Plain char signedness

`z3-char-signedness` warns about implicitly converting known negative values to
plain `char`, including conditional branches and `EOF`:

```cpp
char sign = negative ? -1 : 1;
```

Plain `char` may be signed or unsigned. Use `int` or `signed char` for negative
numeric values, and `int` for a byte-or-EOF result. The check also warns about
passing plain or signed `char` to the one-argument C character-classification
and case-conversion functions. Convert bytes to `unsigned char` first:

```cpp
std::isspace(static_cast<unsigned char>(byte));
```

The diagnostics are the same under `-fsigned-char` and `-funsigned-char`.
Explicit casts, nonnegative ASCII constants, and integer stream results passed
to character classification are accepted. The check does not track values across
variables or function calls, or flag every arithmetic operation involving `char`.
It offers no automatic fixes. Use `NOLINT(z3-char-signedness)` for justified exceptions.

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

By default, all checks listed in `checks.py` run together in one clang-tidy
invocation per translation unit, so each file is parsed once. To select a subset,
pass `--check z3-char-signedness` (repeat `--check` to select more than one).

## CI reports

The **Determinism Linter** workflow (`ast-order-warning-report.yml`) runs
the linter on changed sources and transitive header
dependents on PRs, using `clang-scan-deps` on both base and the PR merge result.
The base is the merge commit's first parent, the base branch tip at scan time,
not `pull_request.base.sha`, which is where the branch forked from the base.
Generated file changes are included. Build configuration or checker changes trigger
full scans; master and nightly/manual runs also scan everything. Scans use all CPUs
and cache completed reports. Compiler or scanner failures fail the job.

`ast-order-warning-comment.yml` updates one PR comment with total and per-check
counts, the checked scope, and a collapsed warning diff identifying each check.
Updates display **EDITED** with the UTC date
and time. Counts on PRs cover the affected files. Stale and incomplete comparisons
are rejected. The comment workflow runs trusted code from the default branch and
reads a bounded, validated report; it must be on that branch to post comments.
