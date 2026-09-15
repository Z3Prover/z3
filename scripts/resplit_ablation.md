# Resplit ablation setup (not study results)

## Design and scope

`resplit_ablation.json` is the authoritative nine-arm parameter matrix.
`all-on` is **nseq with integrated seq_monadic**, not `theory_seq`.
Eight arms vary only P/E/R; `no-factorization` additionally changes only
`smt.nseq.regex_factorization_threshold=0`. Views, monadic landing/leaf,
equation/substitution lengths, exact requested-length checks and model
validation remain enabled. New gates preserve the old defaults: P=true,
E=false, R=true. All-on intentionally opts into E and the constituent features.

The manuscript labels are `all-on`, `no-parikh`, `no-equation-regex`,
`no-reversal`, `all-off`, and separate `no-factorization`. The remaining
factorial arms are `p0-e0-r1`, `p0-e1-r0`, `p1-e0-r0`. These are label-only
changes to the previously validated parameter vectors. Previously frozen
manifests/results retain their `P1E1R1`-style labels and must not be rewritten.
Prepare a new plan to use the readable names; `--only` always refers to labels
in that plan's own `configurations.json`.

The P gate disables optional Parikh/count and regex-length abstractions. It
does **not** mean "remove string lengths", "disable arithmetic", or "disable
the view side conditions". E is regular abstraction of word equations used
only for refutation. R controls forward-work-exhaustion reverse retries in the
nseq monadic leaf engine, not all suffix processing. Factorization-off removes
algebraic `seq_split` factorization, **not** derivative-state decomposition.

### Exact feature boundaries

All parameter names in this table start with `smt.nseq.`:

| Group | Parameter | Solver default | Study on / off |
|---|---|---|---|
| P | `parikh_abstraction` | true | true / false |
| E | `equation_abstraction` | false | true / false |
| R | `reverse_retry` | true | true / false |
| Separate factorization ablation | `regex_factorization_threshold` | 1 | 1 / 0 |

Declarations: `src/params/smt_params_helper.pyg:144-166`; nseq integration:
`src/smt/theory_nseq.cpp:1020-1042`. All-on explicitly enables the constituent
`parikh`, `abelian`, `regex_parikh`, monadic split/landing/leaf/refutation/root
features and `view_length_constraints`; use the JSON, not solver defaults.

**P=false removes these optional paths:** root and descendant plain-regex
length bounds; supported classical-regex exact visit-count length encodings;
the per-node stride/congruence pass and its legacy quick-conflict attempt;
abelian equation-count cancellation; regex character-profile/congruence
refutation; and optional gradient exclusions, shortest-word lower-bound jumps
and lazy exact-length strengthening during length-coherence repair.
Setting only `nseq.parikh=false` does not disable this entire group.

The boundary retains original constraints, equation/substitution length
equalities, nonnegativity, arithmetic/path feasibility, view-length side
conditions, exact requested-length membership checks, impossible-value
blocking, and witness/model validation. Thus it removes derived strengthening,
not acceptance obligations or all uses of length information. See
`src/smt/seq/seq_nielsen.cpp:751-835,890-903,950-1020`,
`seq_nielsen_search.cpp:32-48`, `seq_nielsen.h:1415-1422` and
`src/smt/theory_nseq.cpp:2190-2342`.

Intervals, strides and character profiles generally over-approximate. A stride
of one does not establish realizability of every length. The supported
normalized classical visit-count encoding gives an exact **length set**, not
the word language or a witness; unsupported extended regex constructs discard
that encoding rather than pretending it is exact (`seq_parikh.cpp:178-318`).
The legacy quick-bound path's independent effectiveness is not claimed: it
still queries bounds on a String term, and activating it with `len(x)` requires
separate branch/dependency analysis. Gate tests are not a whole-solver proof.

**E uses the current node's ground, plain memberships**, rebuilt on every
root/per-node check. Memberships for the same token are conjunctive; repeated
occurrences are nevertheless independent segments. Unconstrained tokens fall
back to Sigma*, literals to singleton languages, and symbolic units to Sigma.
E neither imports arithmetic length bounds nor computes a fixed point of all
equation-implied variable languages. It omits Q-gated land views and non-ground
memberships. Concatenations are flattened before lookup, so memberships on a
whole concatenation are not directly consulted. Only an empty intersection
refutes; a nonempty relaxation never establishes SAT for the equation.
See `src/smt/seq/seq_nielsen_regex.cpp:862-894` and
`src/ast/rewriter/seq_eq_approx.cpp:91-135`.

**`no-equation-regex` means this additional equation-side refutation pass is
off, not that all equation-regex information is disabled.** Membership-subject
widening remains enabled, including use of plain regexes and gated views;
equation substitutions may expose new membership subjects to it. Ordinary
membership propagation, regex prechecks and monadic/Nielsen reasoning remain.
See `seq_nielsen_simplify.cpp:864-885` and `seq_nielsen_automaton.cpp:486-554`.

R changes only the nseq monadic leaf decision's retry policy, not native suffix
simplification or forward landing enumeration. Factorization-off disables the
algebraic factorizer without disabling derivative-state views or monadic
decomposition (`seq_nielsen_regex.cpp:655-657,898-918`).

## Current-source port and effective configuration

The ablation changes from `e9ac2a4162d9fca382b31bb3fabe214923857bbb`
have been ported onto `e2bfa52a4fef91ba908e6dd1fb2bef5408671e47`.
The former was based on `b113f38309081b3d3482988bd0e18029d551e971`,
38 commits behind this base. The port retains the current shared
`ast/rewriter/seq_parikh` implementation and the inlined Nielsen per-node
pass; it does not restore the removed `seq_parikh::apply_to_node`.
Plain-membership guards remain at the Nielsen adapter boundary.

The consolidated exact-length encoder also accepts an explicit arithmetic
length target. Root generation uses `compute_length_expr`, which expands
concatenations and powers, so its target is not always syntactically
`str.len(str_key)`. Only the final equality uses this supplied target; the
current encoder's flow constraints, fallback behavior, and deterministic
visit-count skolem keys are preserved. `nseq_ablation` tests this adapter
contract and the root caller.

**All-on is not the ordinary c3-merge configuration**, even on identical
source. Compared with

```text
z3 -T:10 smt.string_solver=nseq smt.nseq.monadic_leaf=true smt.nseq.regex_parikh=true model_validate=true
```

the unchanged JSON intentionally differs as follows (nseq names below have
the prefix `smt.nseq.`):

| Setting | Ordinary command on the current base | Study all-on |
|---|---|---|
| `parikh` | false | true |
| `abelian` | false | true |
| `monadic_split` | false | true |
| `monadic_landing` | false | true |
| `monadic_leaf_refute` | false | true |
| Additional equation-intersection precheck | absent on the base; `equation_abstraction=false` after port | true |
| `tactic.default_tactic` | unset: strategic dispatch and preprocessing | `smt` |
| Command-line allocator limit | no explicit `-memory` limit | `-memory:4096` in the study runner |

The leaf/refute/root budgets are **300000/30000/50000 in both configurations**.
The refute budget is ordinarily inactive for non-root equation-bearing nodes
because `monadic_leaf_refute=false`; all-on enables these additional calls.
Both configurations ask at the root, use monadic leaf reasoning and
regex-Parikh with modulus bound 5, retain view-length constraints, retry
backwards after forward work exhaustion, and use factorization threshold 1,
lazy factorization, dynamic decomposition, eager Nielsen propagation and
unlimited Nielsen depth/node counts. Both random seeds are 0. The new
`smt.seq.parikh_*` settings belong to the legacy `seq` solver; they do not
replace these nseq controls.

Default sources are `src/params/smt_params_helper.pyg` and
`src/params/tactic_params.pyg`, copied by `src/params/smt_params.cpp` and
installed on the graph by `src/smt/theory_nseq.cpp`. Budget selection is in
`nielsen_graph::apply_monadic_leaf`. The unset tactic follows
`smt_strategic_solver.cpp` / `default_tactic.cpp`; forcing `smt` bypasses
that tactic's simplification and preamble, so it is not merely an explicit
spelling of the default.

Keep the ordinary command as a separately labelled competitor and keep the
nine-arm JSON unchanged. Source, corpus and resource alignment are necessary
for a controlled comparison, but do not make distinct parameter vectors
equivalent. A normalized same-binary comparison, if desired, must be a
separately labelled diagnostic, not a silent replacement of all-on.
Historical aggregate timing alone cannot attribute a difference to E,
budgets, preprocessing, or another constituent feature.

## Historical located infrastructure / corpus

`noodler-bench.yml` is in **Z3Prover/bench**, not Z3Prover/z3.
Verified with authenticated `gh search code` and read-only `gh api`:

* Workflow and runner inspected at
  `d15e4515236d7baaa9e03a966fb1062ea9dcc5b5`:
  `.github/workflows/noodler-bench.yml`, `scripts/noodler_bench.py`.
* Existing local corpus: `C:\git\bench\inputs\regexes`, bench HEAD
  `13a4c28e426b6508b06950e445da38430b01e162`, regex subtree tree
  `af6690f1125a218e4f50b43e59f8b26486ad4185`.
* Families `ClemensRegex`, `MargusRegex`; subdirectories are retained in results.
  At this local pin: 1476 `.smt2` files. This is **not** silently equated with
  the latest remote corpus: the ClemensRegex subtree differs at the inspected
  remote workflow SHA; MargusRegex is identical.
* The historical paper `eval/perf3way.py` references `paper/bench`, which is
  absent here. We use the located comparison corpus, not an invented substitute.
* No code downloaded from GitHub was executed. No changes to the bench checkout.

Reuse: same corpus layout, sorted paths and evenly spaced sampling convention,
same private-app checkout mechanism and rise runners. The older runners are
not suitable for trustworthy ablations unmodified: they lack full raw/provenance
records and strict parameter/multi-query handling. Thus the new standard-library
driver reuses their corpus/selection convention, not their permissive parsers.

## Local invocation (PowerShell, from C:\git\z3)

Use the existing Release CMake/Ninja build and MSVC developer environment.
The CMake executable target is **shell**, not `z3`.

```powershell
cmake --build build-release --target shell test-z3 --parallel 8
.\build-release\test-z3.exe nseq_ablation seq_monadic_retry seq_eq_approx seq_profile_abs seq_parikh rewriter_seq_parikh
python -m unittest discover -s scripts\tests -p test_resplit_ablation.py

# Record only AFTER the successful build. Pristine source is the default.
# --allow-dirty is an explicit attestation: archive HEAD + binary diff +
# every untracked nonignored source file, not a misleading pristine SHA.
python scripts\resplit_ablation.py record-build `
  --source . --build-dir build-release --z3 build-release\z3.exe `
  --build-command "cmake --build build-release --target shell test-z3 --parallel 8" `
  --allow-dirty --out .z3-agent\resplit\build-record

# Preparation hashes/validates the entire subtree but solves NOTHING.
# Four evenly spaced unique cases for smoke; omit --limit for the full plan.
python scripts\resplit_ablation.py prepare `
  --corpus C:\git\bench\inputs\regexes `
  --corpus-sha 13a4c28e426b6508b06950e445da38430b01e162 `
  --limit 4 --out .z3-agent\resplit\plan

python scripts\resplit_ablation.py run `
  --study .z3-agent\resplit\plan `
  --build-record .z3-agent\resplit\build-record\build.json `
  --z3 build-release\z3.exe --timeout 10 --memory-mb 4096 `
  --out .z3-agent\resplit\results
```

Every output directory must be **new**; existing outputs are never overwritten.
No dependency installation is required. CMake/Ninja and Python must already
exist. Use the same invocation on Linux with its binary path. Do not edit source
between recording and running: the runner rejects source/binary/build-configuration
drift, and checks source/binary again at the end. The build record is an explicit
operator attestation, not proof that an arbitrary existing binary matches source;
recording an unrebuilt binary is invalid usage.

When reusing a downloaded build-record archive, `run --source` locates the
checked-out source and `--build-dir` locates the **saved** build evidence.
They override stale absolute locations recorded on the build machine, not
the recorded source identity, evidence hashes or binary hash. CI uses:

```bash
python3 z3/scripts/resplit_ablation.py run \
  --study "arms/$CONFIG_NAME/plan" --only "$CONFIG_NAME" --repeats 1 \
  --z3 build-record/z3 --build-record build-record/build.json \
  --source z3 --build-dir build-record \
  --timeout "$TIMEOUT" --memory-mb "$MEMORY_MB" --out "arms/$CONFIG_NAME/results"
```

## Validation, selection, metadata

Only a single ordinary `check-sat` is accepted. Push/pop/reset, multiple queries,
check-sat-assuming, optimization and unknown commands are rejected and listed.
There is no "last verdict wins". The lexer understands comments, doubled string
quotes and quoted symbols. It does not search raw SMT text for constraints.

Original bytes are saved. Execution removes presentation requests
(`get-model`, `get-value`, `get-info`, `get-assignment`, `exit`) following
check-sat, and harmless `:print-success` / `:produce-models` options; each removal
is recorded. These are replaced by one check-sat and reason-unknown request.
Input solver/resource options are rejected, never allowed to override the study.
`model_validate=true` still checks SAT models. Full model text is not collected.
Z3 remains the SMT-LIB sort/syntax authority; diagnostics invalidate runs.

Deduplication is token-structural (ignores whitespace/comments and set-info,
not string contents), not semantic equivalence or alpha-renaming. Canonical
representative = first POSIX-sorted path. Alias paths/families and byte hashes
remain in `manifest.json`. A known sat/unsat annotation on an alias is propagated
to the representative; conflicting known annotations in the duplicate group
make the manifest non-runnable. Sampling is after validation/deduplication,
unlike historical runners: do not compare their same-sized samples by index.
Always pair by manifest input identity. An excluded input requires inspection
and explicit `--accept-exclusions`; the workflow intentionally does not supply it.
Local `prepare` also supports a corpus at the Git repository root, not only a
subdirectory; the study output must remain outside the corpus. The workflow
continues to select within the pinned `inputs/regexes` subtree.

`pure-membership` is certified only for a narrow Boolean combination of
memberships over String constants/variables/concatenations and recognized ground
regex constructors. Equations/lengths are conservatively recognized from parsed
operators and known string terms. Definitions, lets, quantifiers, and unsupported
forms remain `unclassified`; this label must not be reported as pure membership.
No filename-based truth inference. `:status` is metadata, not a proof.
There is no automatic ground truth by solver majority vote.

## Resource and measurement policy

One process at a time (`jobs=1`), no warmup, seeds fixed. **Local nine-arm runs
interleave configurations**, rotating arm order deterministically by case and
repetition. `--repeats N` preserves every repetition.

**CI uses sequential arm blocks:** nine matrix jobs, each running one `--only`
configuration with one repetition, `max-parallel: 1`, and the same selected
runner label. GitHub does not guarantee the listed matrix order. This is not
the locally interleaved protocol; report the order difference rather than
pooling the two as identical experiments. A label must select stable hardware
and hostname: merge checks those recorded fields exactly, not just the label.
Neither a runner label nor job serialization guarantees absence of unrelated
machine load.

Every arm gets the same `-t:1000*T`, `-T:T`, Python total wall deadline T,
and `-memory:M`. The parent deadline includes process startup and is not
extended for reversal; cleanup/kill latency is retained in elapsed time.
OS scheduling may delay deadline enforcement. Completed runs beyond T are
timeouts, not solved data points.

Memory is Z3's **allocator limit in MB**, not a hard RSS/cgroup/Windows-job limit.
OOM is an error, not a timeout. This is a documented portability limit; for hard
RSS isolation use the same external container/cgroup for every arm. Do not claim
RSS enforcement or measured peak RSS. Native memory statistics are retained.

Forward/reversed monadic calls can each consume their internal work allowance.
R-off gets the full forward allowance; R-on gets no additional wall/memory
allowance. Monadic budgets: leaf=300000, refute=30000, root=50000.
Zero leaf/root means engine default (currently 1000000); refute zero means no
separate cap. E has 4096 product states per equation. Resource polls can terminate
these operations earlier. Internal work budgets are not total process budgets.

Preflight invokes every complete parameter vector on a tiny string problem.
Unknown parameters, parser errors, crashes, OOM, invalid-model diagnostics,
missing/multiple verdicts and annotation/sat-unsat contradictions are errors.
Unknown is preserved unless reason-unknown says timeout/canceled.
Errors never get hidden behind an earlier `sat`. Failure exits nonzero.

## Outputs and analysis

* `manifest.json`, `configurations.json`: corpus SHA/tree, all file hashes,
  aliases/exclusions, selected cases, actual parameter matrix.
* `build-record/`: binary SHA256/version, Git HEAD + binary diff and untracked
  source archive, CMakeCache/build.ninja/compiler identification, build command.
* `inputs/`, `original/`, `runner.py`, `environment.json`: replay inputs, exact
  runner, machine/platform/Python, sequential order, limits and repetition count.
* `preflight/*.{stdout,stderr,json}`: parameter acceptance, including failures.
* `raw/<id>/<repeat>-<arm>.{stdout,stderr,json}`: complete raw output, return code,
  argv, elapsed wall time, reason, extracted statistics. Raw statistics remain
  authoritative if an unfamiliar statistic is not parsed.
* `runs.jsonl`, `runs.csv`: flushed after every run; partial results survive failure.
* `summary.json`: sat/unsat/unknown/timeout/error counts overall and by
  family/category; all-on-vs-arm paired solved counts and joint-decision geometric
  mean of **other/all-on** elapsed times (above 1 means all-on faster).
  Joint ratios exclude undecided/error cases. PAR-2 charges **2*T for every
  timeout, unknown or error**, reports totals, and does not impute solve times.
  Errors/contradictions set `valid_for_comparison=false`; no paper-ready result
  may be inferred from that summary. Compare counts as well as survivor ratios.
* `failure.json` where applicable: preflight/provenance failures.

For a single-arm result, `summary.complete=true` means **that arm** completed,
not that all nine arms have run. There are no within-root paired comparisons
between separately executed arms. Strict merging requires complete input
blocks whose non-overlapping configurations form the full nine-arm union.
A block may contain multiple arms (for local testing); CI uses one arm per
block. It compares:

* Identical `source_identity`, `binary_sha256`, and `build_evidence`.
* Identical frozen configurations and manifests, ignoring only the manifest's
  absolute `corpus` and `repository` locations.
* Identical environment fields `platform`, `machine`, `hostname`, `processor`,
  `cpu_count`, `timeout_seconds`, `memory_mb`, `memory_policy`, `jobs`, `repeats`.

Merge computes paired metrics and cross-arm contradictions while retaining
each input root's invalidity: aggregation cannot turn an invalid root valid.
Missing, duplicate or incompatible arms must fail, never produce a silently
successful partial campaign. The shared build artifact provides the exact
same executable bytes, not independently rebuilt binaries with matching SHAs
only at the source level.

In the workflow, downloaded artifacts have this layout:

```text
partials/
  resplit-arm-all-on/results/...
  resplit-arm-no-parikh/results/...
  ... (all nine arm archives, each also containing plan/)
merged/
  runs.jsonl
  runs.csv
  summary.json
  ... (merge provenance, hashes and raw-directory references)
```

Exact Linux merge command, after downloading **all** arm archives:

```bash
python3 z3/scripts/resplit_ablation.py merge \
  --results partials/resplit-arm-*/results --out merged
```

`merged` must be new. The workflow checks for nine result directories before
calling the strict merger; counting directories alone is not validation.
Keep `partials/` **alongside** `merged/`: combined summaries and hashes are not
a replacement for raw stdout/stderr, inputs, statistics and failure evidence.
The merged artifact bundles both, and individual arm artifacts are retained
as well. Keep the shared build artifact containing the actual executable.

No resumption or automatic successful fallback is implemented. Use a new
workflow dispatch for a retry rather than mixing attempts or overwriting
immutable artifacts. Inspect run count versus selected cases × configurations
× repetitions; preserve failed/incomplete runs separately.

## Existing other-solver comparison: exact all-on reuse

The inspected `bench/scripts/noodler_bench.py` uses `C3_MERGE_OPTS` with only
`string_solver=nseq`, `monadic_leaf=true`, `regex_parikh=true`, `model_validate=true`.
Its `no-leaf`/`no-parikh` arms are **not** these ablations. Historical CSVs must
not be relabelled or merged into this study as all-on measurements.

Export the exact all-on argv, without manually transcribing flags:

```powershell
python scripts\resplit_ablation.py argv --name all-on
# Run the all-on arm on exactly the already frozen manifest:
python scripts\resplit_ablation.py run --only all-on `
  --study .z3-agent\resplit\plan --build-record .z3-agent\resplit\build-record\build.json `
  --z3 build-release\z3.exe --timeout 10 --memory-mb 4096 `
  --out .z3-agent\resplit\comparison-all-on
```

For the next owned **bench** comparison workflow revision, the exact replacement
for `C3_MERGE_OPTS` (in a reviewed checkout containing these z3 scripts) is:

```python
import sys
sys.path.insert(0, str(Path("z3-c3-merge/scripts").resolve()))
from resplit_ablation import configurations
C3_MERGE_OPTS = configurations(Path("z3-c3-merge/scripts/resplit_ablation.json"))[1]["all-on"]
```

Use the same pinned solver binary, selected manifest/original identities and
limits; remove/rename legacy no-leaf/no-parikh arms rather than calling them
P/E/R. The command above is the authoritative standalone all-on reuse path
until that separate repository is changed. The existing external solver runs
have different timeout/raw/provenance handling; their old CSV timings are not
automatically a matched experiment. This implementation does not modify or
dispatch the out-of-scope bench workflow or download/build external solvers.

## New manual workflow

The dispatchable workflow is published on the default branch of
**Z3Prover/bench**, alongside `noodler-bench.yml`. The file in this Z3
checkout is its template; dispatch the benchmark repository's workflow,
passing an immutable Z3 commit containing the solver and driver changes.

`.github/workflows/resplit-ablation.yml` uses the same rise-runner labels and
private bench checkout as `noodler-bench.yml`. Inputs: full `solver_sha` containing
these changes; full `corpus_sha`; optional `corpus_subdir`; `limit` (default 4);
`campaign` confirmation for >20/all inputs; `timeout`; `memory_mb`; `runner`.
The job graph is:

1. **Build once.** Check out the immutable solver SHA, build Release and run
   targeted tests, create `build-record/build.json` and existing evidence, and
   copy the built executable to `build-record/z3`. Upload **one immutable
   `resplit-build-record` artifact**. All arm jobs download this artifact by
   its artifact ID; none builds another solver.
2. **Nine sequential arm jobs.** Each checks out the same solver/corpus pins,
   mints its own private-bench app token, and prepares the same corpus
   selection. Plans/results have separate `arms/<configuration>/` directories.
   Source/corpus checkout paths are shared within the run, and generated files
   are isolated under a run/attempt-specific directory on persistent runners.
   The binary is the shared `build-record/z3` (execute permission restored
   after download), with relocation overrides shown above. `fail-fast: false`
   lets later arms finish even if another fails; `max-parallel: 1` prevents
   simultaneous arm runs. Each arm always attempts to upload its plan and raw
   results as `resplit-arm-<configuration>`.
3. **Strict merge.** After all arms, even if an arm failed, download the arm
   artifacts separately under `partials/` and run `merge`. An absent/failed
   arm cannot become a successful study. Always attempt to upload
   `resplit-ablation-merged`, containing both `merged/` and the retained raw
   `partials/`, including evidence from unsuccessful merges. A failed build
   prevents the arm and merge jobs from running.

Each arm has a **350-minute job timeout**, but solving is admitted only when:

```text
(selected_count + 1 preflight) * timeout_seconds <= 300 * 60
```

This guard runs after preparation, using the actual selected count after
validation/deduplication; CI fixes repetitions to one. It reserves 50 minutes
for checkout, preparation, process/file overhead and artifact transfers. An
oversized selection fails with an explicit recommendation to choose a smaller
`corpus_subdir` or `limit` (or reduce timeout); no silent sampling or limit
change occurs. At the pinned full corpus, `(1011+1)*10 = 10120` seconds
(168 minutes 40 seconds) fits **per arm**. The nine-arm campaign can still take
more than a day; there is no claim that the entire study fits one 350-minute
job. Local interleaved runs remain available without this CI scheduling cap.

All three job types use the same chosen runner label. Workflow concurrency
serializes this workflow's campaigns on that label with
`cancel-in-progress: false`; it does not cancel builds. This does not serialize
unrelated workflows or workloads.

Requires a runner revision implementing `run --source` / `--build-dir` and the
strict `merge` command, plus `Z3_CI_APP_CLIENT_ID` and
`Z3_CI_APP_PRIVATE_KEY` configured for corpus read access in this workflow's
repository and Python plus a C++20 compiler. If CMake or Ninja is missing,
the build job restores a private copy using the existing benchmark workflow's
tool sources; it does not require sudo or change system installations.
It has no push/schedule trigger. Uncommitted local
changes cannot be selected as `solver_sha`.
