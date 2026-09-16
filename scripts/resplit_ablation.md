# Default-based nseq ablation harness (not results)

## Schema 2: one baseline, six individual flips

`resplit_ablation.json` is the authoritative parameter specification. Schema 2
replaces the artificial nine-arm All-on / factorial design with **seven**
default-based configurations. `common` is the explicit baseline; each other
configuration has one override. Both this standalone harness and Bench's
importer validate the exact baseline, names, order, parameter types and flips.

The native default base is
`d6d8966631b156508ec681faf102a8f8ed33736c`, after the former E2 base
`e2bfa52a4fef91ba908e6dd1fb2bef5408671e47`. It defaults
`smt.nseq.monadic_leaf=true` and `smt.nseq.regex_parikh=true`.
The top-level string solver still defaults to **seq**, so every study arm
explicitly selects `smt.string_solver=nseq`.

| Configuration | Only difference from the baseline |
|---|---|
| `z3-tacas` | None |
| `z3-tacas-no-monadic-leaf` | `smt.nseq.monadic_leaf=true` → false |
| `z3-tacas-no-regex-parikh` | `smt.nseq.regex_parikh=true` → false |
| `z3-tacas-equation-abstraction` | `smt.nseq.equation_abstraction=false` → true |
| `z3-tacas-no-factorization` | `smt.nseq.regex_factorization_threshold=1` → 0 |
| `z3-tacas-no-reversal` | `smt.nseq.reverse_retry=true` → false |
| `z3-tacas-abelian` | `smt.nseq.abelian=false` → true |

**There is no eighth `parikh` arm.** In the combined Bench campaign, `z3-tacas`
is exactly this baseline using the same instrumented binary and settings.
It is measured only once, not again as an `ablation-*` competitor.

Instrumentation is restricted to **E/R controls and their counters**. The
old instrumentation's additional length-handling fixes are excluded from
`z3-tacas` and this evaluation, preserving the pinned native default source's
baseline semantics.

### Semantics and fixed settings

Names below have prefix `smt.nseq.` unless fully qualified:

- `monadic_leaf` invokes integrated `seq_monadic` over supported memberships.
  Refuting cores can close nodes even with word equations. SAT witnesses
  require no residual word equations or disequalities and retain an unchanged
  fallback branch. `monadic_leaf_root=true` adds the initial root call:
  an applicable SAT witness is parked until normal expansion, while an
  equation-bearing root uses only refutations. Extra later equation-bearing
  calls remain off (`monadic_leaf_refute=false`). Ordinary membership
  reasoning is not disabled with the leaf.
- `regex_parikh` refutes through per-letter regex-profile congruences, with
  length refinement; `regex_parikh_mod=5` remains fixed.
- `equation_abstraction` is **instrumentation only**, default false. It is
  regular-language relaxation of word equations, not equation-only Parikh.
  The current node's ground plain memberships constrain repeated tokens as
  independent segments; unconstrained tokens relax to Sigma*, literals to
  singleton languages. Empty intersection refutes; nonempty proves nothing
  about satisfiability of the word equation. No arithmetic-length fixed point
  or view-dependent language inference is claimed.
- `reverse_retry` is **instrumentation only**, default true to match native
  nseq's hard-coded retry. It affects the monadic leaf decision after forward
  work exhaustion, not all suffix simplification or landing enumeration.
  The seq orientation enum is `forward`, `reversed`, `retry`, not `reverse`.
- Factorization threshold zero disables algebraic factorization, not
  derivative-state views or dynamic decomposition.
- `abelian=false` is the cheap native per-letter equation balance check,
  including inconsistent literal counts when variable multisets cancel.
- **`parikh_abstraction` is a historical umbrella gate**, formerly covering
  optional count and regex-length strengthening, not just equation reasoning.
  It is **not registered or passed in the new campaign**. It remains available
  only for explicit schema-1 replay with that study's pinned old source; no
  silent reinterpretation as the E/R-only campaign is permitted.
- **`parikh=false` is native and active**, including calls from `search_dfs`.
  It enables regex-length abstraction (stride and supported exact-length
  encodings). It is neither dead code nor a full Parikh-image computation.
  Supported exact length sets do not establish a word-language witness.
  The pinned native path runs from `src/smt/theory_nseq.cpp:1020` through
  `src/smt/seq/seq_nielsen_search.cpp:475` to `apply_parikh_to_node` at line 32
  of the latter file. It stays off in all seven arms; no eighth arm is approved.

All arms explicitly spell out the six studied settings, both
native default-enabled flags, and the following frozen options:

| Fixed option | Value |
|---|---|
| `tactic.default_tactic` | Empty string |
| `model_validate` | true |
| `smt.random_seed`, `sat.random_seed` | 0, 0 |
| `parikh`, `monadic_split`, `monadic_landing`, `monadic_leaf_refute` | false |
| `monadic_leaf_budget`, `monadic_leaf_budget_refute`, `monadic_leaf_budget_root` | 300000, 30000, 50000 |
| `monadic_leaf_root`, `regex_precheck`, `view_length_constraints` | true |
| `regex_factorization_eager` | false |
| `regex_dynamic_decomposition`, `eager` | true |
| `block_compression`, `exploration_budget` | 1, 512 |
| `signature`, `fine_wilf`, `axiomatize_diseq` | false |
| `max_depth`, `max_nodes`, `harvest` | 0 |

Normal strategic dispatch and preprocessing remain enabled.
**Do not force `tactic.default_tactic=smt`.** The empty assignment is accepted
by Z3; forcing `smt` is a different experimental condition.

Native defaults are declared in `src/params/smt_params_helper.pyg` and
`src/params/tactic_params.pyg`; the standalone tests compare the common nseq
values to the actual parameter declarations. The full-source pin and archived
`-p` listing make additional omitted defaults auditable.

## Whole evaluation lives in Z3Prover/bench

Use Bench's `.github/workflows/noodler-bench.yml` and
`docs/noodler-bench.md` for the **complete comparison**. It builds the
instrumented solver once and shares a cryptographically checked bundle across
four sequential input shards, eight workers per shard, one repetition,
10-second total wall cutoff and 4096-MB Z3 allocator cap.

The corpus is pinned to
`5efc3492055cf879cd9847f26b9dad6c151eb77b`: all **2,711 .smt2 files**,
2,413 ClemensRegex and 298 MargusRegex. The new protocol does not deduplicate
or infer semantic equivalence from a commit message. The former corpus at
`e4997560a00b178e29c62e1014536aa45361c971` had 1,986 inputs / 1,521
token-distinct groups; old campaign artifacts are not relabelled/overwritten.

The combined campaign has **16 configurations / 43,376 measurements**:
seven native; Z3 5.0.0 defaults, Z3 5.1.0 monadic on/default and off;
development Z3 monadic on/off; Noodler 1.6.1, cvc5 1.3.4, Ostrich 2.1,
and Ostrich + Parikh. Z3 5.0.0 receives **no** unsupported regex_monadic flag.
All comparator sources and foreign assets are immutable pins; c3/c3mv are
disabled by default.

Workflow tools come from the recorded Bench `GITHUB_SHA`, separate from the
corpus checkout. Compatibility compares the pinned native base against the
pinned instrumented source, never current branch HEAD. Retained binaries,
release archives, hashes, exact arguments and source/build evidence support
replay even after branches advance. Timing can still vary with hardware,
compiler/toolchain, unrelated system load and scheduling.

## Standalone local diagnostics

This standard-library-only harness does not build/download/run benchmarks
implicitly. `prepare` hashes and validates the corpus without solving.
Use the existing Release CMake/Ninja build; the executable target is `shell`.
Commands below are PowerShell and output paths must be new.

```powershell
python -m unittest discover -s scripts\tests -p test_resplit_ablation.py

# After a successful instrumented build, attest its actual source/binary.
python scripts\resplit_ablation.py record-build `
  --source . --build-dir build-release --z3 build-release\z3.exe `
  --native-base-sha d6d8966631b156508ec681faf102a8f8ed33736c `
  --build-command "cmake --build build-release --target shell test-z3 --parallel 8" `
  --out .z3-agent\resplit\build-record

# Four diagnostic files only; omit --limit to prepare all files without solving.
python scripts\resplit_ablation.py prepare `
  --corpus C:\git\bench\inputs\regexes `
  --corpus-sha 5efc3492055cf879cd9847f26b9dad6c151eb77b `
  --limit 4 --out .z3-agent\resplit\plan

python scripts\resplit_ablation.py run `
  --study .z3-agent\resplit\plan `
  --build-record .z3-agent\resplit\build-record\build.json `
  --z3 build-release\z3.exe --timeout 10 --memory-mb 4096 --repeats 1 `
  --out .z3-agent\resplit\results
```

`--allow-dirty` is an explicit build attestation exception: it archives the
HEAD-relative binary diff (index and worktree) plus untracked source bytes.
It does not make an unrebuilt binary a valid build. Source, binary, compiler/
CMake/Ninja evidence and parameter-listing hashes are checked when running;
source/binary are checked again afterwards. `--source` and `--build-dir`
can relocate checkouts/build records without changing their identities.
`argv` displays the expanded baseline by default; `--name` selects another
configuration. `--only` uses names from the plan's own frozen JSON.

### Selection, normalization and historical schemas

Schema 2 selects **all validated files**, including token duplicates, in
POSIX-sorted path order; a nonzero limit evenly selects files afterwards.
No representative-sampling claim is made. Token identities/aliases are
diagnostics, not semantic equivalence. Contradictory duplicate annotations
make a plan non-runnable.

Schema 1 retains its historical nine-arm names, options and token-deduplicated
selection. Its All-on forces different preprocessing and enables additional
passes. It is not today's `z3-tacas`, and cannot be combined with schema-2
data. Replay historical results with their original source/workflow/manifest.

Only one ordinary `check-sat` is accepted. Incremental/multiple queries,
solver/resource options and unsupported commands are listed as rejections,
never silently dropped. `run` refuses exclusions unless explicitly accepted.
The structural lexer understands strings, quoted symbols and comments.
Presentation commands are removed; original and normalized bytes are saved.
The standalone protocol adds `get-info :reason-unknown` and requests statistics.
It differs from Bench's normalization/scheduling; do not pool their timings.
`pure-membership` is only a conservative syntactic certificate, not a
filename-based inference. An expected-status annotation is not a proof.

### Resources, failures and outputs

Standalone local execution uses **one worker**, rotating configuration order
deterministically by input/repetition. Bench's standalone smoke workflow
(`resplit-ablation.yml`) uses seven sequential per-arm jobs, one repetition,
default `limit=20`. These are diagnostics, not the full campaign. The full
2,711 × 10-second serial worst case exceeds its 300-minute per-arm allowance;
the workflow refuses it and directs full runs to `noodler-bench.yml`.
The staged historical workflow in this Z3 source tree is not the campaign
entry point; use the maintained Bench workflows.

All arms share the same process/query timers and total Python wall deadline,
including startup. Retry does not reset them. Monadic internal work budgets
are not extra process budgets. Memory is Z3's allocator cap, **not** a
portable OS RSS/cgroup limit. Cleanup/scheduling latency stays in wall time.

Preflight runs every complete vector on a tiny string formula. Parser/option
errors, crashes, invalid models, OOM and missing/multiple verdicts are errors,
even after a printed `sat`; timeout/unknown remain distinct. Invalid-model
diagnostics remain in raw streams (standalone categorizes them as errors).
Failures and contradictory verdicts invalidate comparison and return nonzero.

Outputs retain `manifest.json`, `configurations.json`, source/build records,
binary hash/version and `parameters.stdout/stderr`, `inputs/`, `original/`,
runner/environment metadata, complete preflight/raw stdout/stderr/argv/exit
status/timings/statistics, and flushed `runs.jsonl`/`runs.csv`.
Z3 `-p` reports **registered defaults**, not runtime overrides; exact per-arm
argv is authoritative. Bench additionally archives per-configuration listings
with explicit-option overlays. Neither introspects tactic-internal tuning.

`summary.json` reports counts and baseline-vs-arm paired coverage, joint-
decision geometric mean of **other/baseline** times, and PAR-2 charging 2*T
for every undecided/error run. Survivor ratios are not overall speedups.
Unique answers are not correctness-certified by majority vote.

`merge` requires complete disjoint configuration blocks covering the frozen
matrix, matching corpus/configuration/source/binary/build/native-base/limits/
hardware metadata. Retain all original arm archives alongside merged reports.
An individual arm's `complete=true` does not certify the entire seven-arm
campaign. Errors and incomplete/mismatched blocks must never be published as
a successful comparison.
