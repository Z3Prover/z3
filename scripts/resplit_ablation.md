# Default-based nseq PERF harness (not results)

## Schema 3: five arms in exact PERF order

`resplit_ablation.json` is the authoritative parameter specification. Schema 3
defines **five** default-based configurations. `common` is the explicit
baseline; each other
configuration has one override. Both this standalone harness and Bench's
importer validate the exact baseline, names, order, parameter types and flips.

Native base **N**, `e06e93676ef8e4920be8c5c22e0e0df527c576d8`, promotes
the minimal E adapter/control with public
default `smt.nseq.equation_abstraction=true`. **H** adds R-only instrumentation.
Bench's corresponding workflow defaults record their reviewed full SHA pins.
Historical D/G are not compatible substitutes for this schema.
Native `monadic_leaf=true` and `regex_parikh=true` remain defaults.
The top-level string solver still defaults to **seq**, so every study arm
explicitly selects `smt.string_solver=nseq`.

All names below have prefix `smt.nseq.`:

| ID | P: regex_parikh | E: equation_abstraction | R: reverse_retry | F: regex_factorization_threshold |
|---|---|---|---|---|
| `TTTT` | true | true | true | 1 |
| `FTTT` | false | true | true | 1 |
| `TFTT` | true | false | true | 1 |
| `TTFT` | true | true | false | 1 |
| `TTTF` | true | true | true | 0 |

F's Boolean labels map to **numeric 1/0**; the native parameter remains a
**UINT**, not Boolean. Leaf=true, abelian=false and parikh=false are fixed:
no leaf/abelian/parikh arms. Bench emits the comparison baseline once as `TTTT`,
not again under `z3-tacas` or an `ablation-*` ID. Every arm uses one fresh H binary.

Instrumentation is restricted to **R**, E now being native/default true. The
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
- `equation_abstraction` is **native**, with public default true. It is
  regular-language relaxation of word equations, not equation-only Parikh.
  The current node's ground plain memberships constrain repeated tokens as
  independent segments; unconstrained tokens relax to Sigma*, literals to
  singleton languages. Empty intersection refutes; nonempty proves nothing
  about satisfiability of the word equation. No arithmetic-length fixed point
  or view-dependent language inference is claimed.
  The private graph's E stays false until `final_check` applies the public
  setting, preserving early-eager semantics despite the new public default.
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
  silent reinterpretation as schema 2 or 3 is permitted.
- **`parikh=false` is native and active**, including calls from `search_dfs`.
  It enables regex-length abstraction (stride and supported exact-length
  encodings). It is neither dead code nor a full Parikh-image computation.
  Supported exact length sets do not establish a word-language witness.
  It stays off in all five arms.

All arms explicitly spell out the four studied settings, both
native default-enabled flags, and the following frozen options:

| Fixed option | Value |
|---|---|
| `tactic.default_tactic` | Empty string |
| `model_validate` | true |
| `smt.random_seed`, `sat.random_seed` | 0, 0 |
| `monadic_leaf` | true |
| `abelian`, `parikh`, `monadic_split`, `monadic_landing`, `monadic_leaf_refute` | false |
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
`src/params/tactic_params.pyg`. `validate-source` checks every common nseq
default and BOOL/UINT type against the actual source before workflow builds;
unit fixtures cover wrong E defaults, missing R and Boolean F. The full-source
pin and archived `-p` listing make additional omitted defaults auditable.

## Whole evaluation lives in Z3Prover/bench

Use Bench's `.github/workflows/noodler-bench.yml` and
`docs/noodler-bench.md` with **`native_only=true`** for the approved full
five-native rerun. It builds the
instrumented solver once and shares a cryptographically checked bundle across
four sequential input shards, eight workers per shard, one repetition,
10-second total wall cutoff and 4096-MB Z3 allocator cap.

The corpus is pinned to
`5efc3492055cf879cd9847f26b9dad6c151eb77b`: all **2,711 .smt2 files**,
2,413 ClemensRegex and 298 MargusRegex. The new protocol does not deduplicate
or infer semantic equivalence from a commit message. The former corpus at
`e4997560a00b178e29c62e1014536aa45361c971` had 1,986 inputs / 1,521
token-distinct groups; old campaign artifacts are not relabelled/overwritten.

The approved run is **5 configurations / 13,555 measurements**. A future full
comparison (`native_only=false`) has **14 configurations / 37,954 measurements**:
five native; Z3 5.0.0 defaults, Z3 5.1.0 monadic on/default and off;
development Z3 monadic on/off; Noodler 1.6.1, cvc5 1.3.4, Ostrich 2.1,
and Ostrich + Parikh. Z3 5.0.0 receives **no** unsupported regex_monadic flag.
All comparator sources and foreign assets are immutable pins; c3/c3mv are
disabled by default. Native-only mode still builds/verifies/smoke-tests the
full shared comparator bundle, but measures only the five native arms.

Workflow tools come from the recorded Bench `GITHUB_SHA`, separate from the
corpus checkout. Compatibility compares the pinned native base against the
pinned instrumented source, never current branch HEAD. Retained binaries,
release archives, hashes, exact arguments and source/build evidence support
replay even after branches advance. Timing can still vary with hardware,
compiler/toolchain, unrelated system load and scheduling.
The retained workflow/source tag is `tacas-perf-20260916`.
Historical tags remain unchanged.

## Standalone local diagnostics

This standard-library-only harness does not build/download/run benchmarks
implicitly. `prepare` hashes and validates the corpus without solving.
Use the existing Release CMake/Ninja build; the executable target is `shell`.
Commands below are PowerShell and output paths must be new.

```powershell
python -m unittest discover -s scripts\tests -p test_resplit_ablation.py

# Requires the reviewed N + R-only H source, not old D/G.
python scripts\resplit_ablation.py validate-source --source .

# After a successful instrumented build, attest its actual source/binary.
python scripts\resplit_ablation.py record-build `
  --source . --build-dir build-release --z3 build-release\z3.exe `
  --native-base-sha e06e93676ef8e4920be8c5c22e0e0df527c576d8 `
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

Schemas 2 and 3 select **all validated files**, including token duplicates, in
POSIX-sorted path order; a nonzero limit evenly selects files afterwards.
No representative-sampling claim is made. Token identities/aliases are
diagnostics, not semantic equivalence. Contradictory duplicate annotations
make a plan non-runnable.

Schema 1 retains its historical nine-arm names, options and token-deduplicated
selection. Its All-on forces different preprocessing and enables additional
passes. It is not today's baseline. Schema 2 retains exactly its seven default-based
arms and its execution-error-fatal policy. Replay either historical schema
with its original source/workflow/manifest, never reinterpreting old records.

Historical G `3e218489200202d926848819603e3873833fe861` used E=false:
only its E-on and baseline match parameter vectors TTTT and TFTT. Its P/R/F-off
vectors are **FFTT/TFFT/TFTF**, not new FTTT/TTFT/TTTF. Leaf-off and abelian-on
violate new fixed settings. These mappings permit **no row reuse or relabelling**:
all five new H arms must run freshly on the same new build. The old completed
seven-arm campaign, including its invalid comparison verdict, remains immutable.

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
(`resplit-ablation.yml`) uses five sequential per-arm jobs, one repetition,
default `limit=20`. These are diagnostics, not the full campaign. The full
2,711 × 10-second serial worst case exceeds its 300-minute per-arm allowance;
the workflow refuses it even with `campaign=true, limit=0`. Full runs use
`noodler-bench.yml` with `native_only=true`.
The staged historical workflow in this Z3 source tree is not the campaign
entry point; use the maintained Bench workflows.

All arms share the same process/query timers and total Python wall deadline,
including startup. Retry does not reset them. Monadic internal work budgets
are not extra process budgets. Memory is Z3's allocator cap, **not** a
portable OS RSS/cgroup limit. Cleanup/scheduling latency stays in wall time.

Preflight runs every complete vector on a tiny string formula; setup/option
failures remain fatal. During **schema-3 measurements**, crashes, parser errors,
OOM and other execution errors are unsuccessful, retained outcomes rather
than an automatic whole-campaign failure. Counts and `execution_errors` make
them conspicuous; each incurs full PAR-2 penalty. Native zero errors with leaf
fixed true is expected, not guaranteed or a separate gate.

**Invalid models remain fatal**, classified before generic errors/timeouts even
after printed SAT. Multiple answers to one query are fatal protocol errors,
even when accompanied by a crash, diagnostic, or timeout.
Contradictory decided verdicts, annotation violations,
incomplete/duplicate/corrupt records and input/source/binary/provenance/argv
mismatches also fail. The standalone schema-1/schema-2 behavior is preserved:
execution failures invalidate those historical comparisons. A passing new
gate does not claim error-free execution or correctness certification.

Outputs retain `manifest.json`, `configurations.json`, source/build records,
binary hash/version and `parameters.stdout/stderr`, `inputs/`, `original/`,
runner/environment metadata, complete preflight/raw stdout/stderr/argv/exit
status/timings/statistics, and flushed `runs.jsonl`/`runs.csv`.
Schema 3 adds `evidence.json`, covering result-file hashes. Merge verifies
these, original/normalized input hashes, raw JSON/argv, and classifications
recomputed from raw streams; tolerated generic errors cannot hide invalid models.
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
An individual arm's `complete=true` does not certify the entire five-arm
campaign. Tolerated errors must accompany its counts and penalties; incomplete,
mismatched or scientifically invalid blocks cannot become a passing comparison.
