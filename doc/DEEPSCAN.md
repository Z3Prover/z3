# DeepScan findings and fixes

This report follows [#11751](https://github.com/Z3Prover/z3/issues/11751).
It implements the two bounded bookkeeping improvements recommended there,
not every optimization hypothesis in the historical profile corpus. Profile
sample shares are not predicted whole-program speedups.

## Implemented findings

### Sequence evaluation cache: clear touched entries, not the high-water range

Sources: [Z3Prover/bench#8929](https://github.com/Z3Prover/bench/issues/8929)
and [Z3Prover/bench#8339](https://github.com/Z3Prover/bench/issues/8339).

`theory_seq::eval_cache::reset` previously reset the vector's size while
retaining its capacity. The next insertion initialized all slots through
`2 * expr_id + 1`, including untouched slots, after every invalidation.

The cache now retains its initialized high-water range and clears only keys
recorded in its existing expression trail. Reset work is proportional to
insertions since the previous reset, rather than the largest expression id.
Duplicate insertions are safe. Both cached expressions and dependencies are
cleared before releasing the trail's expression references, so recycled AST
ids cannot expose stale entries. This adds neither an epoch array nor a
second touched-key allocation. The old implementation already retained the
backing allocation; the change does not add a new unbounded cache.

The `seq_rewriter` tests cover high-id sparse keys, overwritten entries,
reinsertion, invalidation on solution updates and scope pop, restored
solutions, and temporary keys released between reset/insert cycles.

### LP registration: reuse the returned column instead of probing again

Source: [Z3Prover/bench#8931](https://github.com/Z3Prover/bench/issues/8931).

Both arithmetic backends checked registration before calling the already
idempotent `lar_solver::add_var`. Model-equality code then looked up the
column or checked registration again after ensuring it existed.

Registration now delegates directly to `add_var`, and `ensure_column`
returns its column for the callers to reuse. Null and Complex terms retain
their existing exclusions. The external/local map, integer metadata,
sentinel handling, column trails, and shrink/pop behavior are unchanged;
there is no dense-id assumption affecting Diophantine or HNF users.

This removes redundant API-level probes. The measurements below do **not**
establish an independent LP speedup; the measured overall gain is primarily
the sequence-cache change.

## Reproducible measurements

Baseline: `a2fd7e6b1acf117b5dcc8b5051c48c95cfb516ee`; candidates are that
revision with only the cache change, or both production changes above.
Windows x64, AMD EPYC 7763, MSVC 14.51.36231, CMake/Ninja Release build,
`Z3_USE_LIB_GMP=OFF`. Processes ran serially on a shared host, without CPU
isolation. Each table entry is the median of five runs; variant order was
rotated between trials. Times include launching Z3 and reading the input.

The original QF_SLIA input was recovered from the `profiled-benchmark`
artifact of [Z3Prover/bench run 43941030739](https://github.com/Z3Prover/bench/actions/runs/43941030739).
Its SHA-256 is
`a90995edf1369dbf88e688ebd9756783de8738ecb7e939696753e2de4c589232`.
Artifact availability is subject to GitHub retention. The original source
URL is redacted in the finding, so the hash and artifact identify the input
without inventing a permanent download location.

All target runs used seeds `smt.random_seed=0`, `sat.random_seed=0` and a
120-second subprocess timeout, without a shortened resource limit. The
monadic case preserves the reported `smt.seq.regex_monadic=true` setting;
the default case sets it to false. Model validation was timed separately.

| Workload | Baseline ms | Cache only ms | Both fixes ms | Both vs baseline |
| --- | ---: | ---: | ---: | ---: |
| Original input, regex monadic | 2458 | 2232 | 2199 | -10.5% |
| Original input, default regex | 2452 | 2174 | 2210 | -9.9% |
| Original input, monadic + model validation | 2463 | 2165 | 2195 | -10.9% |
| 4096-variable incremental LP, SMT | 1747 | 1730 | 1747 | no measured gain |
| 4096-variable incremental LP, SAT/EUF | 5267 | 5268 | 5260 | within noise |

The monadic target ranged from 2399-2522 ms before and 2183-2423 ms after
both changes. All variants returned `sat`, with identical resource counts:
6,519,007 without model validation and 6,519,695 with it. Z3 peak memory
remained 30.43 MB. The LP controls returned `sat`, `unsat`, `sat`, including
after pop; all variants had identical resource counts and peak memory:
1,626,961 / 93.34 MB for SMT and 815,015 / 69.47 MB for SAT/EUF. Additional
256-variable controls likewise showed no independent LP improvement.
Hardware instruction, cache-miss, and allocator counters were not collected;
there is no claim of an independently measured change in those metrics.

To retrieve and run the target against separately built baseline/candidate
executables, repeating in alternating order:

```powershell
gh run download 43941030739 --repo Z3Prover/bench --name profiled-benchmark --dir benchmark
Get-FileHash -Algorithm SHA256 benchmark\benchmark.smt2
Get-Content -Raw benchmark\benchmark.smt2 | & $z3 -in -st smt.seq.regex_monadic=true smt.random_seed=0 sat.random_seed=0
```

The LP control is generated as follows; also run it with `sat.euf=true`:

```python
from pathlib import Path
text = '(set-option :model_validate true)(declare-fun f (Real) Real)\n'
for i in range(4096):
    text += (f'(declare-const x{i} Real)(assert (<= 0 x{i}))'
             f'(assert (<= x{i} 1))(assert (>= (f x{i}) 0))\n')
text += '(check-sat)(push 1)(assert (< x0 0))(check-sat)(pop 1)(check-sat)\n'
Path('linear.smt2').write_text(text)
```

## Correctness validation

Built `shell`, `test-z3`, and `build_z3_python_bindings`. The `seq_rewriter`
and `lp_evidence` modules pass, including the new cache tests and existing
arithmetic proof checks. CLI solving/model/help and Python binding smoke
checks pass. Model-validation benchmark runs pass for both arithmetic
backends. The full default suite reports **131 passed, 1 failed**.

The failure is the existing `check_proof_mode_guards` expectation in `smt_context`
at `src\test\smt_context.cpp:1331`. It was reproduced with all six changed
source files stashed and `test-z3` rebuilt on unmodified baseline
`a2fd7e6b1` (exit 114, same assertion). It is not hidden or fixed as part of
these performance changes.

## Remaining leads and dispositions

These are follow-up candidates from #11751, not newly reproduced findings:

| Lead | Disposition |
| --- | --- |
| Exact-division leading-term rescans | Defer heap/incremental ordering work until graded-lex ordering and coefficient-cancellation tests accompany a reproduced polynomial workload. |
| NLSAT clause satisfaction scans | Defer blockers/versioned caches pending staged-assignment and backtracking invalidation design. |
| Polynomial powers, sign evaluation, monomial interning | Defer cross-call memoization and hash/layout changes pending lifetime, assignment-version, collision, and memory measurements. |
| Arithmetic explanations and nonlinear intervals | Defer interval reuse and prefix/suffix products pending dependency, strictness, zero/unbounded, and propagation tests; do not repeat witness batching already merged in #10029. |
| SMT watches and congruence locality | Defer blocker/prefetch/table-layout changes pending instruction/cache-miss measurements and deletion/root-update validation; the existing watched filter is not reimplemented. |
| Regex-monadic product allocation | Defer arena/flat-key changes pending a separate product-search profile and depth-aware caching design; this is not evidence about default regex workloads. |
| Large memset profiles | Unresolved caller attribution is not an actionable diagnosis of a particular vector or bit-vector implementation. |
| Karatsuba | Do not resurrect reverted experiments without reproducing operand-size distributions and previous performance gates. |
| HNF pivots and LP model delta | Reuse the already merged #10073, #10497, and #10217 work rather than reimplementing it. |
