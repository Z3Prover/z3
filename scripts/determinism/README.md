# Solver determinism

Build several Z3 configurations from the same source and compare their solver
traces and output **byte for byte, treating CRLF and LF line endings as equivalent**.
Each input also runs twice with each binary, so a configuration must agree with
itself. No lines are sorted, AST IDs renamed, or addresses replaced. Other
whitespace remains significant, including spaces inside string literals.

The structured trace (`trace=true`) includes expression creation with AST IDs,
SMT assignments, conflicts and instantiations. The runner works with unmodified
Z3 and captures whatever its trace writer emits, including pretty-printer nodes.
Platform-specific pointer formatting is reported as a difference too. Line endings
are normalized only for comparison; raw artifacts retain their original bytes.

## Local use

Requires Python 3.11+, CMake, Ninja and the compilers for the selected profiles.
Linux, macOS and Windows are supported. `ccache` is used when installed. For
example, Ubuntu 24.04 provides
`g++-14 clang-18 libc++-18-dev libc++abi-18-dev ninja-build ccache`.

Check out the corpus at the revision recorded in `corpus.json`:

```sh
git clone https://github.com/Z3Prover/z3test ../z3test
revision=$(python3 -c 'import json; print(json.load(open("scripts/determinism/corpus.json"))["revision"])')
git -C ../z3test checkout "$revision"
```

On Windows, set `git config --global core.autocrlf false` before checking out
the corpus to preserve the same line endings on every OS. The workflow does this for both
repositories. The PowerShell equivalent of reading the revision is
`$revision = (Get-Content scripts/determinism/corpus.json -Raw | ConvertFrom-Json).revision`.

On Linux, run all five configurations with a total of eight build jobs:

```sh
python3 scripts/determinism/run.py matrix \
  --suite ../z3test --gcc g++-14 --clang clang++-18 --jobs 8
```

The configurations are:

- `gcc`: GCC with libstdc++.
- `gcc-unsigned-char`: the same GCC with `-funsigned-char`, testing the opposite
  signedness from the default on the Linux x64 CI runner.
- `clang`: Clang with the selected GCC's libstdc++ headers.
- `libcxx`: Clang with libc++.
- `libcxx-random`: Clang with libc++'s unspecified-order randomization, seed 1.
- `apple-clang`: macOS Apple Clang and the system libc++.
- `msvc`: Windows MSVC and the Microsoft C++ standard library, using Ninja.

The local default is the five Linux profiles on Linux, `apple-clang` on macOS,
and `msvc` on Windows. For macOS, install Ninja and optionally ccache with Homebrew,
then run:

```sh
python3 scripts/determinism/run.py matrix --suite ../z3test --clang /usr/bin/clang++
```

On Windows, use a **Developer PowerShell for Visual Studio 2022** targeting x64,
with Python, CMake and Ninja on PATH:

```powershell
python scripts/determinism/run.py matrix --suite ../z3test --profiles msvc
```

`--msvc` selects another `cl.exe` path within that developer environment. Executable
names, process termination, UTF-8 metadata and artifact paths are handled per OS.
Reports from different machines can be copied into one directory and passed to
`compare --profiles gcc gcc-unsigned-char clang libcxx libcxx-random apple-clang msvc`; every named
configuration must be present and use the same source, corpus and run settings.

Compilers are configurable; `--gcc g++-16 --clang clang++-22` works on hosts
with those versions. For a private libc++ installation, use `--libcxx-include`
for its `include/c++/v1` directory and `--libcxx-lib` for its library directory.

Use `--profiles gcc clang` for a smaller matrix. Build directories and the
compiler cache are reused under `build/determinism`; each run gets a new timestamped
report directory. `--work` changes that location. The total build concurrency is
bounded by `--jobs`, divided among the selected configurations. `CCACHE_DIR` and
`CCACHE_MAXSIZE` can override the local cache defaults. Use a separate `--work`
directory when switching compiler or library installations.

To use existing binaries:

```sh
python3 scripts/determinism/run.py run --suite ../z3test --out /tmp/z3-runs \
  --binary gcc=/path/to/gcc/z3 --binary clang=/path/to/clang/z3
python3 scripts/determinism/run.py compare --input /tmp/z3-runs \
  --profiles gcc clang --out /tmp/z3-comparison
```

`run` checks successful completion; `compare` checks equality. The combined
`matrix` command does both and exits nonzero for a mismatch or incomplete run.
`build --profile NAME` is also available for separate build jobs.

## What is checked

The committed manifest selects 100 files from a pinned Z3Prover/z3test revision.
The sample takes ten files per syntactic
category (arrays, bitvectors, datatypes, floating point, linear arithmetic,
nonlinear arithmetic, optimization, other, quantifiers, strings/sequences),
ordered by a fixed filename hash. It was selected before comparing results.
Files with explicit timeout/seed/thread/trace controls, reset/include, statistics
queries, expected errors, or no check-sat were excluded. `--corpus` accepts another
manifest of the same form. Editing a testcase does not require updating its entry.
To use newer testcases in CI, update the pinned revision; add or remove paths when
changing which cases run.

The manifest also includes miscellaneous testcases from `cases/`.

Every run uses a fresh process, a private directory, identical input bytes,
fixed default solver seeds, single-threaded solving, and `LC_ALL=C`. Three files are
compared separately: `ast.trace`, `stdout`, and `stderr`. Normal verbosity defaults
to zero; structured tracing is still enabled. `--verbosity 10` enables additional
diagnostics, but some diagnostic paths still print time/memory or iterate unordered
containers. These differences are reported and fail the comparison too.

The default `rlimit=1000000` bounds solver work. An external 45-second watchdog
and a 128 MiB limit per output file guard against runaway jobs. POSIX uses an OS
file-size limit; Windows checks output sizes every 100 ms, so a file can briefly
exceed the limit before termination. Oversized completed output also fails.
The watchdog kills the process group on POSIX and the process tree on Windows.
A run must exit zero, produce no SMT-LIB error, and end its trace with `[eof]`
followed by LF or CRLF. Timeouts, crashes, truncated output, missing artifacts,
and incompatible run settings cannot pass. A completed
`unknown` answer is compared like any other answer; this is a determinism check,
not an expected-answer regression suite.

The report contains exact-match counts and the first differing lines, and case identifiers
for the preserved inputs and logs. It displays remaining carriage returns as `\r`;
the captured files retain their original bytes.
JSON metadata records compiler and build commands, OS/architecture, source revision
and tracked source diff hash, binary hashes, corpus, seeds, exit statuses and output
hashes. Artifact hashes are rechecked on comparison.
Elapsed times in `run.json`, `runs.json` and build metadata are diagnostic only;
they are not part of the byte-for-byte comparison. Compare the three output
channels, not whole artifact directories, to inspect solver differences.

The trace is not an exhaustive log of every engine, and tracing may affect AST
creation. Internal wall-clock `try_for` tactics can still affect behavior even
with a resource limit; such differences need investigation. Passing a small corpus
with one sorting seed does not prove universal determinism.

## Randomized sorting

The randomized profile defines both:

```text
_LIBCPP_DEBUG_RANDOMIZE_UNSPECIFIED_STABILITY
_LIBCPP_DEBUG_RANDOMIZE_UNSPECIFIED_STABILITY_SEED=1
```

libc++ uses a separate generator for this randomization, consuming neither Z3's
random generator nor C `rand()`. We fix the seed to make the randomized sorting
reproducible. Without an explicit seed, libc++ may seed from an address, so ASLR
can change the shuffle order between runs. Use `--sort-seed N`
to test another order; this is a compile-time option and requires rebuilding the
randomized configuration. The ordinary libc++ profile gives a direct control.
The feature covers unspecified ordering in `sort`, `partial_sort` and `nth_element`,
not Z3's custom sorting routines. See the [libc++ design document](https://libcxx.llvm.org/DesignDocs/UnspecifiedBehaviorRandomization.html);
the seed macro above follows the installed headers, whose spelling differs from
some versions of that document.

## GitHub Actions

`.github/workflows/determinism.yml` runs on every PR, pushes to master, and manual dispatch.

| Runner | Configuration |
|---|---|
| Ubuntu 24.04, x64 | GCC 14 / libstdc++ |
| Ubuntu 24.04, x64 | GCC 14 / libstdc++, `-funsigned-char` |
| Ubuntu 24.04, x64 | Clang 18 / libstdc++ |
| Ubuntu 24.04, x64 | Clang 18 / libc++ 18 |
| Ubuntu 24.04, x64 | Clang 18 / libc++ 18, randomized sorting seed 1 |
| macOS 15, ARM64 | Apple Clang / system libc++ |
| Windows Server 2022, x64 | Visual Studio 2022 MSVC / Microsoft STL |

Each OS/configuration has its own compiler cache. The corpus revision is pinned.
Compiler/package updates within these runner images remain possible;
compiler and host versions are recorded. macOS also adds ARM64 coverage, while
Windows exercises its LLP64 data model and a different standard library.

The Linux comparison job checks that all seven complete result sets exist, verifies their
provenance and output hashes, and fails on any difference beyond CRLF/LF line endings. It writes a job
summary with expandable first differences and retains raw runs and build logs as
artifacts. Fork PRs use the ordinary read-only `pull_request` workflow. Pushes to master also warm the caches
that later PRs can restore. macOS and Windows results are compared directly with
the Linux GCC baseline as well as with their own second runs.

When a PR run fails or times out, `determinism-comment.yml` posts a comment linking
to that run's summary, logs and artifacts. Later failures update the same comment
with an **EDITED** date and the failed commit. Successful and cancelled runs do not
post comments; an existing comment remains a record of the linked failure.
Runs for an outdated PR head are skipped.

The comment workflow uses `workflow_run` so it can comment on fork PRs. It must
be present on the repository's default branch before comments will run. It uses
only GitHub run/PR metadata, without checking out PR code or downloading artifacts,
and only its reporting job receives `pull-requests: write` permission.
