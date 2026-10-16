# Standalone OCaml proof-checker executable

**Latest cross-logic measurements (2026-10-15):**
[SMT-LIB cross-cut report](SMTLIB_CROSSCUT_REPORT.md) reruns 900 inputs
across nine logics with the checked-definition/`distinct` checker,
separating full certification, obligations, rejection, and phase costs.
The measurements below retain their historical configurations and scope.

## Goal

Every earlier proof-checking harness in this repo (`tools/extract_z3_proof.py
--check`, and even `--json`'s JSON-instance-`.fst`-per-proof variant)
re-invokes `fstar.exe` once per proof: it type-checks a `.fst` file (either
the full hand-written proof term, or a tiny JSON-instance wrapper) against
the whole Pulse proof-checker development, including an SMT-solver call,
every single time. That is correct but slow (**~10.3s** per proof, dominated
by F*/Z3 startup and re-verification of code that never changes between
runs) and conceptually wrong for a "run this already-verified checker on
new input" workflow: nothing about the *checker itself* changes from proof
to proof, only the *data* (the proof document) does.

This report describes a **compiled, standalone, native executable** built
once from the already Pulse-verified checker (`Z3PulseProofCheckerJson.fst`'s
`check_proof_json`), which at proof-checking time does no F*/fstar.exe
invocation, no re-type-checking, and no SMT-solver call at all — it just
runs ordinary compiled code against the JSON. Measured **~7ms** per proof
(WSL-internal timing, no process-launch overhead), roughly **1500x** faster
than the old per-proof `fstar.exe` path, because the entire cost of
verification was already paid once, at build time, by F*/Pulse itself.

## Why OCaml, and why a hand-written runtime shim

F* ships a `--codegen OCaml` backend (also `FSharp`, `krml`/C, `Plugin`,
...). OCaml was chosen because Pulse's separation-logic-verified, genuinely
*imperative* code (`ref`/`let mut`, not just pure functions) was confirmed
to extract to completely ordinary OCaml — `Pulse_Lib_Reference.alloc`/
`read`/`write` calls over a plain `ref` — with no special restricted subset
needed (unlike krml/Low*, which imposes additional restrictions on what
Pulse/F* code is expressible in C).

This machine has **no OCaml toolchain anywhere** (confirmed by exhaustive
search of `PATH`/`Program Files`/the filesystem). Per explicit instruction,
one was installed **inside WSL** (Ubuntu), since WSL has `gcc`/`make`, and
opam/OCaml are otherwise unavailable natively on Windows:

- Installed `m4`/`unzip` without root via `apt-get download <pkg>` (fetches
  the `.deb` without installing) + `dpkg -x <pkg>.deb ~/bin` (extracts
  without root).
- Installed the static `opam` binary the same way (opam's installer script
  run with `--download-only`, then the binary copied manually into
  `~/bin` — bypassing the installer's usual `sudo cp` step).
- `opam init --bare --disable-sandboxing -a -y` bootstraps an opam root
  without needing root or `bwrap`-sandboxing permissions.
- F* itself ships a **prebuilt** OCaml extraction runtime
  (`lib/fstar/lib/fstar.cmxa`/`fstar.a`, containing precompiled
  `Prims`/`FStar_*` modules) that extracted code is normally expected to
  link against. This was found to be **unusable in this environment**: its
  `.cmi` files require an *exact* OCaml compiler version match (bisected via
  `.cmi` magic-number/interface-hash comparison to **OCaml 5.3.0**
  specifically — 5.2.1 too old, 5.4.1 too new) *and* an exact match of the
  `batteries` library build used when `fstar.cmxa` was itself compiled
  (`fStar_String.cmi` requires a `BatUTF8` interface hash that no
  installable opam `batteries` version 3.1.0–3.11.0 reproduces on OCaml
  5.3.0). No combination of OCaml/batteries versions resolved this.
- **Resolution**: rather than keep chasing exact prebuilt-library version
  matches, inspect which `Prims`/`FStar_*`/`Pulse_Lib_*` symbols the
  *actually extracted* `.ml` files reference (a small, fixed set — about 40
  identifiers, found via `grep` across all extracted files) and hand-write
  a minimal from-scratch OCaml implementation of exactly those symbols,
  with **zero external opam package dependencies**. This sidesteps the
  version-matching problem permanently: the shim only has to agree with
  itself.

## The runtime shim (`fstar/ocaml_runtime/`)

| File | Provides |
|---|---|
| `prims.ml` | Exact `Prims.int`/`nat`/`pos` via Zarith `Z.t`, with arithmetic/comparison operators, Euclidean division/remainder, and `int_zero`/`int_one`/`of_int`/`not`/`pow2`; native `bool`/`string`/`list` aliases |
| `fStar_Pervasives_Native.ml` | `option` aliased to OCaml's native `option` (`type nonrec 'a option = 'a option = None | Some of 'a`); `fst`/`snd` |
| `fStar_List_Tot_Base.ml` | `length`/`rev`/`map`/`append`/`op_At`/`hd`/`mem`/`index`, wrappers over `Stdlib.List` with exact integer conversions |
| `fStar_Char.ml` | Native integer codepoints for extracted raw character patterns; `int_of_char` converts to `Z.t`, while `u32_of_char` retains the native codepoint |
| `fStar_UInt32.ml` | Native integer character-facing representation; `v` converts to exact `Prims.int` |
| `fStar_UInt.ml` | Fixed-width modular arithmetic, masks, shifts, rotations, and bitwise operations via Zarith |
| `fStar_String.ml` | `strlen`/`list_of_string`/`string_of_list`, byte-wise via `Stdlib.String`/`Stdlib.Char` (sufficient: the JSON proof format is pure ASCII) |
| `fStar_FunctionalExtensionality.ml` | `restricted_t` as a plain function-type alias (type-level only; never invoked at runtime by this checker) |
| `pulse_Lib_Reference.ml` | `ref`/`alloc`/`read`/`write` over a native OCaml `ref`, matching the exact (ghost-argument-padded) call shapes the extracted code uses: `alloc () v`, `read r () ()`, `write r v` |
| `pulse_Lib_Dv.ml` | `unreachable () = Stdlib.failwith "..."` |
| `main.ml` | CLI entry point: reads JSON from stdin (no args) or a file (one arg), calls `Z3PulseProofCheckerJson.check_proof_json`, prints `ACCEPT`/`REJECT`, exits `0`/`1`/`2` |

**Exact integers (2026-10-15):** `Prims.int` is now Zarith `Z.t`, not the
previous 63-bit shim. Extracted modules open `Prims`, allowing its exact
operators to shadow OCaml's machine-integer operators without editing
generated code. Arbitrary-size decoded references and arithmetic
certificates must not wrap. Native character patterns remain a separate
representation with explicit integer projections. The runtime is still
handwritten, not formally verified; huge values remain subject to resource
limits. See [the arithmetic integration report](ARITHMETIC_CERTIFICATE_REPORT.md)
for the semantic bridge, certificate checks, and measured coverage.

## Build pipeline (`fstar/tools/build_ocaml_checker.ps1`)

Two phases, fully scripted and reproducible from a clean checkout (given a
one-time WSL + opam switch `fstar53` (OCaml 5.3.0) setup, see the script's
header comment):

1. **Phase 1 (Windows, `fstar.exe`)**:
   - `fstar.exe --codegen OCaml` requires *every* module in the dependency
     graph — including the module being extracted itself, not just its
     dependencies — to already have a `.checked` file on disk ("Cross-module
     inlining expects all modules to be checked first"). A single
     `fstar.exe <file>.fst` invocation also defaults to "fly_deps" mode,
     which rejects multiple file arguments and won't write a `.checked`
     file for the top module unless every dependency was cached in a
     *separate prior* invocation.
   - Solution: invoke `fstar.exe --cache_checked_modules --cache_dir
     --include <dir> --smt <z3.exe> <single-module>.fst` **one module at a
     time**, in (approximately) dependency order, across up to 5 passes
     (modules whose deps aren't cached yet are harmlessly re-verified and
     retried on the next pass) — until all 17 modules (`Z3AstTheory.fst`
     through `Z3PulseProofCheckerJson.fst`) are cached.
   - Then one more `fstar.exe --codegen OCaml --cache_dir ... --extract
     "<module list>" Z3PulseProofCheckerJson.fst` call emits one plain
     `.ml` file per module under `--odir`.
2. **Phase 2 (WSL, `ocamlfind ocamlopt`)**: copies the hand-written shim
   (`ocaml_runtime/*.ml`) and the extracted `.ml` files into a WSL build
   directory, and compiles everything — shim files first, then the
   extracted modules in dependency order, then `main.ml` — into one native
   executable with
   `ocamlfind ocamlopt -package zarith -linkpkg <all files in order> -o checker`.
   The exact integer runtime requires Zarith in the selected opam switch.

Two non-obvious script bugs were found and fixed while validating this
script end-to-end from a clean state (deleted `build_cache`/`build_extract`
and `~/z3checker`, reran from scratch):

- PowerShell's `$ErrorActionPreference = "Stop"` combined with piping
  `fstar.exe`'s stderr output (including harmless warnings, e.g. "Warning
  290") through `Select-String` turned every such warning into a
  *terminating* `NativeCommandError`, aborting the script after the very
  first module even though `fstar.exe` itself succeeded. Fixed by using
  `$ErrorActionPreference = "Continue"` and checking cache-file existence
  / `$LASTEXITCODE` explicitly instead of relying on PowerShell exceptions.
- The here-string used to generate the WSL build shell script
  (`build_wsl_tmp.sh`) was written with Windows (`\r\n`) line endings via
  `Set-Content -Encoding ASCII`, which bash interprets literally (`set -e`
  became `set -e\r`, i.e. an invalid option; and a path ending in `\r`
  doesn't exist), and the non-interactive `wsl -e bash` invocation does not
  source `~/.bashrc`, so `~/bin` (where `opam`/`ocamlfind` live) was never
  on `PATH`. Fixed by writing the script with `\n`-only line endings
  (`[System.IO.File]::WriteAllText` with an explicit replace of `\r\n` to
  `\n`) and explicitly prepending `export PATH="$HOME/bin:$PATH"` inside
  the generated script.

After these fixes, `tools/build_ocaml_checker.ps1` runs start-to-finish
from a fully clean `build_cache`/`build_extract`/`~/z3checker` state and
produces a working `~/z3checker/checker` executable, confirming the whole
pipeline — not just the originally hand-run ad hoc commands — is
reproducible.

## Validation

- **Cross-validated against the real Pulse checker**: generated a genuine
  JSON proof document via `tools/extract_z3_proof.py --json` on a real
  `.smt2` benchmark, ran it through both (a) the new compiled executable,
  and (b) `fstar.exe` directly verifying a properly-named JSON-instance
  `.fst` file wrapping the same JSON — both agreed (`ACCEPT` / "All
  verification conditions discharged successfully").
- **Negative test**: fed the executable a malformed/non-JSON input —
  correctly printed `REJECT` and exited with a non-zero status.
- **Performance**: `fstar.exe --check` per proof: **~10.27s** wall-clock
  (F*/Z3 startup + full re-verification). New compiled executable, run
  repeatedly inside WSL (no per-call process-launch overhead counted):
  **~7ms** per invocation. The entire cost difference is explained by the
  old path re-doing verification work (type-checking + SMT) that is
  already complete and will never change, once per proof, while the new
  path does no verification work at proof-check time at all — it only
  interprets already-verified, compiled code against new data.

## Harness integration (`tools/extract_z3_proof.py`)

A new `--fast-check` flag (requiring `--json`) was added alongside the
pre-existing `--check` flag:

```
python tools/extract_z3_proof.py --json --fast-check my_benchmark.smt2
```

This writes the JSON proof document exactly as `--json` always did, then
pipes it (via `wsl -e bash -c "<checker-exe> <wsl-path-to-json>"`,
with the path translated from a Windows path to its corresponding
`/mnt/<drive>/...` WSL path) to the precompiled executable
(`--checker-exe`, default `~/z3checker/checker`) and reports
`ACCEPT`/`REJECT`. Critically, **this path never writes or compiles a new
`.fst` file, and never invokes `fstar.exe`**, satisfying the original
requirement that "the scripts that invoke the proof checker should not
rebuild a new Pulse file" — the checker executable is built exactly once
(via `build_ocaml_checker.ps1`) and reused across every subsequent proof.

The pre-existing `--check` flag (which does still shell out to `fstar.exe`
per proof) is left unchanged, so both the slow/fully-from-source path and
the fast/precompiled path remain available for cross-checking.

## Full refutations (`--full-proof`)

The default, legacy equational-fragment workflow remains unchanged.
The extractor also supports a separate `resolution-v1` document format
that preserves the complete ground refutation DAG:

```powershell
python fstar\tools\extract_z3_proof.py problem.smt2 --full-proof --fast-check --json-out proof.json
```

This format uses the same sort/declaration/expression pools, plus
`assertions` (expression indices), a `proofs` array of
`{"kind": ..., "conclusion": <expr index>, "premises": [<earlier proof index>, ...]}`,
and a `root` proof index. Unsupported steps have kind `trusted` and
retain their original rule name in `rule`; they are not disguised as
equational rewrite leaves.

`Z3ResolutionProofJson.fst` decodes each node into
`Z3UnifiedProof.fst`'s common `proof_node` representation. Its conclusions
and checked premises carry one of three distinct judgments:
`Holds A`, `Equal s t`, or `Observational s t`. Equality conclusions
are classified uniformly whether produced by resolution, MP, or an
equational rule. A single kernel handles inference, hypothesis scopes,
and explicit obligations, without manufacturing `Rewrite`, `Trusted`,
or `REq` wrappers around previously checked premises.
This allows congruence to consume equalities derived by `mp` or
`unit-resolution`. It also handles equality paths for `trans*`, checks
asserted leaves against the declared inputs, tracks hypotheses per
derivation, and requires a `false` root with no open hypotheses.
The checker supports ground inference and explicit ground/quantified
definition introductions, with capture-avoiding expansion as described
below. Quantified conclusions and inputs must be well scoped, including
the sorts of bound variables. Free variables are rejected. This does
not add general quantifier instantiation or Skolemization inference.

### At-most-once DAG checking and indexed caches

Both native JSON checking paths process each proof-array entry at most
once, in topological order. Caches are keyed by the entry's integer ID,
not by recursively hashing its proof term. A shared premise retrieves its
already-computed result; it never recursively checks the premise again.
Self references, forward references, negative indices, and dangling
references are rejected. Cache state starts empty for each document.

The full-proof path already cached `checked_fact` values, including their
hypothesis scopes. The legacy JSON path now does the same bottom-up
computation through `cached_proof`, whose F* refinement proves
`result == fact term` for every cached success **and failure**. The
refinement and its proof are erased during extraction: no recursive
`fact` call is executed to establish or retrieve a cached result.
The Pulse JSON wrapper consumes this result while retaining its previous
postcondition. The separate in-memory `Z3PulseProofChecker.check_proof`
tree API is unchanged; the native JSON CLI no longer invokes that
recursive tree traversal.

The shared persistent binary-trie cache also indexes decoded expressions.
References now take `O(log ID)` lookup time, and expression accumulation
uses list prepend rather than repeatedly copying a growing prefix.
`lemma_index_put` proves that insertion stores the requested key and
leaves all other lookups unchanged. The full-proof speedups below come
from this indexing change, not from adding a proof cache where one
already existed.

The following are medians of three alternating before/after runs on
identical certificates in WSL. Timings include native process startup,
JSON parsing, decoding, and checking, but exclude Z3 proof generation,
F* compilation, and WSL startup. `/usr/bin/time` also records peak RSS.

| Certificate | Proof nodes | Before | After | Speedup |
|---|---:|---:|---:|---:|
| `dead_dnd001` | 32,679 | 1.410 s | 0.608 s | 2.32x |
| `QF_UF_006` (`gensys_brn1083`) | 26,446 | 1.010 s | 0.508 s | 1.99x |
| `QF_UF_094` (`NEQ031_size7`) | 94,000 | 22.552 s | 15.231 s | 1.48x |
| `QF_UF_015` (Sokoban) | 11,714 | 70.305 s | 3.216 s | 21.86x |
| Legacy shared transitivity DAG, depth 40 | 41 | timeout at 5 s | 0.108 s | >46x |

The legacy synthetic DAG has over two trillion node occurrences when
unfolded as a tree, but just 41 indexed proof nodes. Its baseline timing
is a timeout, not a completed run. On `dead_dnd001`, median peak RSS also
drops from 123.7 MiB to 99.5 MiB. All 58 exported QF_UF certificates now
report `ACCEPT` within a 30-second per-proof limit; the slowest takes
14.9 seconds in the four-worker recheck. Acceptance policies and proof
obligation counts are unchanged. Detailed timing/RSS samples and corpus
results are retained under ignored `build_extract` artifacts
`proof_once_benchmarks.json`, `proof_once_benchmarks.db`, and
`proof_once_corpus.json`.

`RUnitRes` now checks a stated consequence instead of requiring a
syntactically rewrapped residual. A residual `[C]` may conclude `C` or
`(or C)`, including when `C` is itself a disjunction. An empty residual
may conclude `false` or `(or)`. Reordering and sound weakening are
accepted provided every surviving literal is covered. Resolving a
formula directly against its negation also works when that formula is
a disjunction. The resolution soundness theorem covers these
representations; dropping a surviving literal is still rejected.

The executable distinguishes:

- `ACCEPT`, exit 0: a closed refutation with no unverified leaf obligations.
  This is relative to the explicit trust policy for definitional axioms below.
- `PARTIAL N`, exit 3: the derivation and hypothesis scopes checked, but
  `N` rewrite/unsupported-rule obligations remain unverified.
- `REJECT`, exit 1: malformed data, invalid inference, undeclared input,
  a non-false root, or an open hypothesis.

Full-proof mode discharges syntactically reflexive rewrites using the
verified total identity rule `identity_rewrite x = Some x`, and n-ary
Boolean `and`/`or` flattening using `Z3BooleanRewrite.flatten_rewrite`.
Flattening recursively splices occurrences of the same connective into
one ordered argument list, preserving duplicates and leaving different
connectives opaque. It supports empty and singleton nested applications;
the result is still an application of the original connective.
The declarations, operator tags, domains, Boolean operands, and result
sort are checked. Reordering, deduplication, and reverse reassociation
are not licensed by this rule.

`lemma_flatten_rewrite_sound` derives semantic equality from the standard
n-ary conjunction/disjunction semantics, using proofs that flattening
preserves their argument-list meanings.

`Z3BooleanNormalForm.fst` additionally proves n-ary De Morgan and
double-negation normalization, implication elimination, contextual
associativity/commutativity/idempotence, singleton collapse, Boolean
constant/complement elimination, and absorption (`a /\ (a \/ b) = a`
and its dual). Structural normalization traverses the recognized Boolean
fragment without a truth-table width limit; recursive set comparison has
fuel 32. `Z3BooleanRewrite.fst` also proves reflexive equality of any sort
reduces to `true`, including inside Boolean contexts.

When these structural rules do not suffice, a depth-8, width-10 Boolean
skeleton uses shared subexpressions as opaque boundaries and checks at
most 1,024 truth-table rows. This reuses the verified generic truth-table
engine in `Z3BoundedBoolEquiv.fst`, **not** its differently numbered
`Z3BasicExprTheory` classifier. A canonical native-tag classifier and
`lemma_boolean_cut_sound` connect the skeleton to the existing standard
Boolean semantics; `lemma_boolean_equiv_sound` proves the resulting
semantic equality. Non-Boolean theory atoms remain opaque except for the
proved reflexive-equality rule. Budget exhaustion means unverified, not
equivalent; no runtime solver call or additional trust assumption is used.

Boolean `ite` is exported with `op_ite` (Z3's declaration name is `if`).
Both Boolean classifiers require three Boolean arguments and a Boolean
result. The verified cut lowers it to `and`/`or`/`not`, reducing constant
conditions or branches directly before normalization. The semantic bridge
uses an explicit standard `ite_sound` interpretation contract; non-Boolean
branches and uninterpreted lookalikes remain opaque to this Boolean engine. Depth/atom budgets
are unchanged. With this support, `cvc\read5.smt2` changes from `PARTIAL 1`
to `ACCEPT`: all 12 rewrite leaves are discharged, including its nested
Boolean ITE chain, under the same default trusted-definition policy.

`Z3ArrayRewrite.fst` adds a separate, fuel-64 contextual equality checker:

- `store(store(a, i, v), i, w) = store(a, i, w)`;
- `store(a, i, select(a, i)) = a`;
- `select(store(a, i, v), i) = v`;
- `select(store(a, i, v), j) = if(i = j, v, select(a, j))`.

These identities compose inside applications, nested stores/selects, array
equalities, and negations. Equality operands may be reversed. Typed ITEs
with scalar or array branches support constant/reflexive conditions,
identical branches, and branches independently proved equal to the same
target. `lemma_equivalent_sound` proves semantic equality by induction
over the recursion budget and argument lists, reusing `Z3ArrayTheory`'s
store/select proofs. The additional `term_ite_sound` model contract is
standard branch-selection semantics, not an assumption that the proposed
rewrite is valid. Select/store matching retains `Z3ArrayLemma`'s flat,
single-index, non-Boolean scalar index/element fragment and exact
declaration, operator-tag, and sort checks. Distinct index names are not
assumed unequal; fresh names are not assumed to denote their definitions.
Unsupported instances and budget exhaustion remain obligations.

The full-proof exporter also preserves exact integer, rational, and
bitvector numeral identities as opaque declarations. Previously, distinct
numerals could decode to identical declarations (e.g. both named `Int`),
which contextual ITE branch checking exposed. Their exact printed values
and numeral-kind parameters now distinguish them; this adds no arithmetic
reasoning or numeral-value interpretation.

These rewrite checks apply to ordinary equality or Boolean observational
equivalence without changing either relation. Other rewrites remain
obligations; Python-side classifications are diagnostic mirrors, not the
acceptance authority. The legacy equational matcher inventory is unchanged.

On `QG-classification\loops6\dead_dnd001.smt2`, all 1,058 rewrite leaves
are now discharged (previously 310 remained after identity and flattening).
Rechecking the 58 successfully exported QF_UF proofs from the existing
seed-42, 100-file sample discharges all 47,776 rewrite leaves. Before
indexed caches, eight workers and a 30-second per-proof checking limit
gave 57 `ACCEPT` results and one timeout; that last proof (`QF_UF_015`,
Sokoban) reported `ACCEPT` in 70.1 seconds with a 120-second limit.
The other 42 sampled
files did not previously produce exported proofs and are not counted as
checked successes. These historical results used the then-default def-axiom
trust policy, not independent validation of those definitions. See the
checked-policy recalibration below for current results.

#### Fresh QF_UF/QF_AX evaluation (2026-10-14)

A complete rerun used the same seed-42 manifest and SHA-256-checked input
files: 100 UNSAT-annotated benchmarks per logic, 32 workers, a 10-second
proof-generation wall-clock limit, a separate 60-second export watchdog,
and a 10-second native-checker limit. Unlike the 58-certificate recheck
above, this reran proof generation and export as well.

| Logic | Proved UNSAT | Exported | ACCEPT | PARTIAL | Checker timeout | Not checked |
|---|---:|---:|---:|---:|---:|---:|
| QF_UF | 93 | 57 | 56 | 0 | 1 | 43 |
| QF_AX | 100 | 99 | 1 | 83 | 15 | 1 |

QF_UF had seven proof-generation timeouts and 36 export timeouts; QF_AX
had one export timeout. There were no checker rejects or errors. The
remaining QF_UF checker timeout was `QF_UF_094` (`NEQ031_size7.smt2`);
the prior 30-second recheck and the fresh 10-second evaluation therefore
measure different limits and workloads.

The 56 accepted QF_UF proofs contained 1,350,973 DAG nodes and no pending
obligations. The 84 validated QF_AX derivations contained 285,459 nodes
and 8,055 pending obligations: 8,031 `th-lemma` and 24 unsupported rewrites.
These counts cover only `ACCEPT`/`PARTIAL` results, not timed-out proofs.
These historical `ACCEPT` results were conditional on the then-trusted
`def-axiom` policy.

For comparison, the previous full-proof evaluation with the same limits
gave QF_UF 1 `ACCEPT`, 48 `PARTIAL`, and 9 checker timeouts from 58 exports;
QF_AX had 83 `PARTIAL` and 16 checker timeouts from 99 exports.
Its validated proofs retained 32,101 QF_UF rewrite obligations and
23,226 QF_AX obligations. Validated sets differ between runs, so aggregate
obligation counts are not a paired per-proof comparison.

The rerun took 187.5 seconds. Its manifest, per-file proofs, phase timings,
checker outputs, source/binary hashes, summary, CSV, and SQLite benchmark
log are retained locally in
`C:\smtlib-benchmarks\proof_check_full_20261014_2054\full`.

#### Fresh rerun with array and Boolean ITE checking (2026-10-15)

The same SHA-256-checked, seed-42 sample of 100 files per logic was
rerun end-to-end after the array and Boolean ITE changes, with unchanged
32-worker, 10-second proving, 60-second export, and 10-second checking
limits. Native protocol counts are authoritative; Python obligation
predictions are retained only as diagnostics.

| Logic | Proved UNSAT | Exported | ACCEPT | PARTIAL | Checker timeout | Not checked |
|---|---:|---:|---:|---:|---:|---:|
| QF_UF | 93 | 57 | 56 | 0 | 1 | 43 |
| QF_AX | 100 | 99 | 71 | 12 | 16 | 1 |

There were no checker rejects, errors, or diagnostic count mismatches.
QF_UF again had seven proving and 36 export timeouts; QF_AX had one
export timeout. The QF_UF checker timeout remains `QF_UF_094`.
The 83 validated QF_AX derivations contain 252,305 DAG nodes, with
7,782 array theory lemma instances discharged and 24 remaining rewrite
obligations across the 12 partial proofs. Accepted QF_UF proofs contain
1,350,973 nodes and no obligations. Acceptance remains relative to the
unchanged default trusted-definition policy.

The sample does not include `cvc\read5.smt2`; its separately demonstrated
Boolean ITE improvement is therefore not measured by these counts.
The earlier array-only paired recheck's 70 QF_AX acceptances and this
run's 71 should not be interpreted as a controlled ITE-only gain:
this is fresh proof generation/export, and timeout sets vary.

The run took 189.2 seconds. The 200 per-file outcomes/statistics,
157 exported proofs, CSV, 200 logged SQLite benchmark runs, original
manifest, source hashes, working-tree patch, and binary provenance are
retained in
`C:\smtlib-benchmarks\proof_check_full_20261015_0345\full`.
The native binary's SHA-256 is
`51863acb94708857ff4fbac0a1903c2cb8971288bcba004f383d6e5536a8cda5`.

#### Contextual array rewrite evaluation (2026-10-15)

The frozen binary above and the new binary were run on the **same 157
byte-identical exported certificates** from the preceding sample, with
32 workers and a 10-second checking deadline. No proof rewriting,
re-export, or trusted-definition policy change was involved.

| Logic | Before ACCEPT / PARTIAL | After ACCEPT / PARTIAL | Remaining obligations before / after | Checker timeouts, both |
|---|---:|---:|---:|---:|
| QF_UF | 56 / 0 | 56 / 0 | 0 / 0 | 1 |
| QF_AX | 70 / 12 | 79 / 3 | 24 / 3 | 17 |

Thus **21 of the 24 outstanding rewrite obligations (87.5%)** were
discharged, making nine previously partial proofs fully accepted under
the existing trust policy. There were no accepted-proof regressions,
rejects, or errors. The paired run's timeout set differs slightly from
the preceding fresh run; coverage comparisons above use only the paired
results, not the earlier 71-acceptance figure. Across the same 82
validated QF_AX certificates, summed process wall times were 110.04 s
before and 110.41 s after (about +0.34% in this single measurement);
QF_UF was 57.76 s versus 57.70 s. These concurrent process-time sums
are not end-to-end elapsed times or a statistically established speedup.

A fresh generation/export/check run on the same SHA-256-verified
100+100-file manifest, with the same 32-worker, 10/60/10-second limits,
gave:

| Logic | Proved UNSAT | Exported | ACCEPT | PARTIAL | Checker timeout | Not checked |
|---|---:|---:|---:|---:|---:|---:|
| QF_UF | 93 | 57 | 56 | 0 | 1 | 43 |
| QF_AX | 100 | 99 | 79 | 3 | 17 | 1 |

It took 189.9 seconds, with no rejects, errors, or diagnostic count
mismatches. The 82 validated QF_AX derivations contain 221,215 DAG nodes,
including 7,575 checked array-theory lemma instances and three remaining
rewrite obligations. Two (`QF_AX_022`, `QF_AX_041`) introduce `k!0`
without a checked definition witness; the third (`QF_AX_085`) needs
stronger guarded-ITE reasoning. They correctly remain `PARTIAL`.
QF_UF again validates 1,350,973 nodes without obligations.

All 47 Python/exporter/native tests pass, including contextual positive
cases, reversed rewrites/guards, unsupported array sorts, fresh names,
unjustified distinct indices, wrong values/bases, recursion-budget
exhaustion, operator spoofing, ill-sorted ITEs, and distinct numerals.
The native dependency build and the executable Boolean/full-DAG F*
regression modules discharge all verification conditions.

Paired results, input hashes, source snapshots, both native binaries, and
fresh results/proofs/CSV/provenance plus 200 SQLite benchmark records are
retained under
`C:\smtlib-benchmarks\proof_check_array_rewrites_20261015_0815`
(`paired` and `full`). The new native binary's SHA-256 is
`0cca221826b0ccf2d48d3fe43075290d05cb2d7fc04980ec835a88b3cb904102`.

The ground Boolean rules `mp~` and `iff~` are checked, not trusted.
Z3's emitted `refl` name is also recognized as reflexivity (the older
`reflexivity` spelling remains accepted).
Observational equality `(~ A B)` is preserved with its own `op_oeq` tag
and the unified kernel's distinct `Observational` judgment.
It is proof-only: it cannot be asserted as an ordinary Boolean fact,
embedded inside a Boolean expression, or consumed by ordinary equality
congruence/resolution. `mp~` requires `~`, whereas ordinary `mp` rejects it.
The explicit `iff~` bridge converts `(= A B)` to `(~ A B)`, not conversely.
Observational reflexivity, symmetry, transitivity, paths, and Boolean
congruence retain `~` conclusions; mixed transitivity can promote Boolean
equality premises through that one-way bridge without ever producing `=`.

The ground observational theory proves observation preservation and derives
equisatisfiability for this checked subset. It does **not** identify Z3's
general equivalence modulo naming with same-model Boolean equality:
naming is handled only through the explicit definition accumulation and
expansion below, before the observational kernel runs. General
Skolemization and unverified NNF steps remain obligations. Non-Boolean
observational equalities remain outside the checked fragment.
Legacy equational-mode `ACCEPT` still has its original, structural-only
meaning and must not be mistaken for certification of an UNSAT refutation.

### SMT array axioms and checked theory lemmas (2026-10-14)

`Z3ArrayTheory.fst` establishes the axiom schemas instantiated by
`src\smt\theory_array_base.cpp` and `theory_array_full.cpp`. Arrays are
extensional functions; a multi-index array is represented by a tuple index.
The mathematical coverage is broader than the executable matching fragment:

| SMT instantiation | Formal result in `Z3ArrayTheory` |
|---|---|
| Store axiom 1, reading at the written index | `lemma_select_store_same` |
| Store axiom 2, reading at another index | `lemma_select_store_diff`, `lemma_store_axiom2`; `lemma_store_axiom2_coordinate` covers each multi-index disequality guard |
| Lambda beta reduction; select congruence | `lemma_select_lambda`, `lemma_select_congruent` |
| Extensionality and its Skolem index | `lemma_array_extensionality`, `lemma_extensionality_witness`, `lemma_extensionality_index_exists`, `lemma_extensionality_axiom` |
| Select of constant, as-array, and n-ary map | `lemma_select_const`, `lemma_select_as_array`, `lemma_select_map_n` |
| Default of constant, as-array, lambda, and n-ary map | `lemma_default_const`, `lemma_default_as_array`, `lemma_default_lambda`, `lemma_default_map_n` |
| Default of store: singleton, finite non-singleton, fresh-index cases | `lemma_default_store_singleton`, `lemma_default_store_finite`, `lemma_default_store_fresh` |
| Epsilon/diagonal witnesses | `lemma_diagonal_fresh`, `lemma_integer_epsilon_fresh` |
| Choice of a satisfying predicate index when one exists | `lemma_choice_witness`, `lemma_choice_axiom` |

The default model uses a shared epsilon index. Store-default invariance
requires that epsilon differ from the stored index: it is **not** proved
as an unconditional identity at an arbitrary fixed index. The singleton
case instead returns the stored value. The finite non-singleton case
establishes the two default/select identities and equality of reads at a
diagonal index different from the write. For integer indices, a finite
list of written indices has an explicitly constructed fresh epsilon.
Extensionality likewise requires a genuine difference witness, not an
arbitrarily chosen index; witness existence is proved for inhabited index
sorts. The as-array default instantiator is currently disabled in C++,
but its mathematical schema is included.

The new `Z3ArrayLemma.fst` recognizes premise-free `th-lemma` conclusions:

```text
select(store(a, i, v), i) = v
(i = j) or (select(store(a, i, v), j) = select(a, j))
(a = b) or not(select(a, array-ext(a, b)) = select(b, array-ext(a, b)))
```

Equality orientation and the two clause literals may be swapped.
Declarations, operator tags, arities, argument/result sorts, base arrays,
indices, and witness arguments must all match. `array-ext` has a distinct
`op_array_ext` tag; an uninterpreted function with that name, an unrelated
array pair, or an arbitrary witness does not discharge the obligation.
The native checker is authoritative; Python classification is only a
diagnostic mirror. Unsupported instances remain `PARTIAL`, not silently
trusted. The current executable fragment covers one-dimensional flat
arrays with non-Boolean scalar index and element sorts, using the existing
`VArr`/`VInt` value representation. Boolean-valued, nested, multi-index,
map/default/choice, and quantified array instances are not newly accepted
by these rules.

`lemma_array_lemma_sound` derives the matched conclusions from the proved
array theory and standard select/store/difference-witness semantics.
`Z3UnifiedProof.model_sound` includes this explicit `array_model`
interpretation contract, just as it includes Boolean and arithmetic
semantics. Matched nodes contribute zero pending obligations; other
theory leaves retain their original obligation. This array evaluation
predated the checked `def-axiom` policy described below.

The broader evaluation also exposed a tightly related structural-rule
gap: `not-or-elim` now accepts a positive literal when the disjunction
contains its negation, as well as the previously supported negative
conclusion. Both polarities have F* soundness and regression checks;
unrelated conclusions are rejected.

#### Seven downloaded logics and paired coverage

The official SMT-LIB 2025 non-incremental archives were downloaded from
[Zenodo record 16740866](https://zenodo.org/records/16740866), verified
against their published MD5 checksums, and extracted under
`C:\smtlib-benchmarks`. Each logic's sample is
`random.Random(42).sample(sorted(UNSAT_annotated_paths), 100)`, with input
SHA-256 hashes retained in the manifest.

Proof generation/export ran once, using 32 workers, a 10-second
proof-generation limit and a separate 60-second export watchdog.
The table compares the frozen previous native checker with the new one
on those archived DAGs, at 32 workers and 10 seconds per check. It also
includes the existing QF_AX sample, without rerunning proof search.
All 109 certificates containing an untagged `array-ext` declaration were
re-exported and checked to be structurally identical to their archived
documents after erasing **only** the new built-in operator tag. Source
and replacement hashes are retained; the other 511 certificates are
unchanged.

| Logic (100 selected each) | Proved UNSAT | Exported | ACCEPT before / after | PARTIAL before / after | REJECT before / after | Checker timeout before / after |
|---|---:|---:|---:|---:|---:|---:|
| QF_LIA | 79 | 69 | 5 / 12 | 25 / 51 | 33 / 0 | 6 / 6 |
| QF_LRA | 58 | 55 | 2 / 3 | 28 / 52 | 25 / 0 | 0 / 0 |
| QF_IDL | 48 | 25 | 1 / 2 | 19 / 20 | 2 / 0 | 3 / 3 |
| QF_UFLIA | 97 | 95 | 3 / 3 | 80 / 92 | 12 / 0 | 0 / 0 |
| QF_AUFLIA | 100 | 100 | 1 / 28 | 87 / 63 | 4 / 0 | 8 / 9 |
| AUFLIA | 91 | 91 | 0 / 0 | 0 / 0 | 91 / 91 | 0 / 0 |
| UFLIA | 86 | 86 | 0 / 0 | 0 / 0 | 86 / 86 | 0 / 0 |
| QF_AX | 100 | 99 | 1 / 70 | 81 / 12 | 0 / 0 | 17 / 17 |

In this historical run, all 177 quantified exports were rejected by the
then-ground-only decoder;
they are not counted as verified. Files that did not export are not
checked. Seven exports failed through Python expression-recursion limits
(three QF_LIA, four QF_IDL); the other missing exports timed out.
The original baseline driver's two reported diagnostic errors
(`QF_LIA_017`, `QF_LRA_023`) were mismatches between Python's predicted
obligation count and the native `PARTIAL` count, not native errors.
The paired table records actual native protocol results, with no such
errors. Timeout counts can vary from earlier runs.

Across the seven new logic samples, accepted refutations increase from
12 to 48. Including QF_AX, they increase from 13 to 118, with no
accepted-proof regressions. On the **same 82 QF_AX proofs validated in
both phases**, pending obligations fall from 7,599 to 24; all remaining
obligations are array rewrites, rather than array `th-lemma` instances.
The same 87 mutually validated QF_AUFLIA proofs fall from 10,765 to
5,133 obligations. The other logics' mutually validated sets keep the
same obligation totals; the `not-or-elim` correction enables additional
proofs to pass structural checking. These remain conditional
refutations under the documented trusted-definition policy, not a
claim of independently checked CNF definitions.

The manifests, download metadata/checksums, baseline results, proof
documents, retag-equivalence checks, and paired native outputs remain in
`C:\smtlib-benchmarks\proof_check_seven_20261014`, principally
`baseline`, `tagged_certificates`, and `array_extension_final`.
The previous/current native SHA-256 hashes for this paired run are
`25e359134f83972e7de8c5fd97cd15b30380cb12c1ff160d63113e491f992cd0`
and `f5ea8d56d71b5c1e6f5910488fd575a871f10a040e33e82e204c7e5e6589a4f5`.
All checker verification conditions and the F* regression module pass;
43 Python/exporter/native tests cover valid and malformed array
instances, witness spoofing, and both `not-or-elim` polarities.

### Definitional axioms and original assertions

`def-axiom` is no longer trusted. A premise-free ordinary Boolean leaf
contributes zero obligations only when its conclusion is independently
checked: a propositional Tseitin tautology, a guarded term-ITE identity,
a verified `distinct` expansion clause,
or a tautology after expanding an accumulated fresh definition witness.
Other well-formed instances contribute one explicit obligation and yield
`PARTIAL`, never certified `ACCEPT`. Malformed/non-leaf instances are
rejected. The obligation-free soundness theorem has no assumption that
`def-axiom` conclusions are true. The same policy applies to the older
`{"kind":"trusted","rule":"def-axiom",...}` encoding.

Only **`asserted` leaves** must match the supplied input assertions.
Membership is structural, not logical equivalence; generated Tseitin
clauses need not themselves be inputs. This is checked in every full-proof
document, with or without:

```powershell
python fstar\tools\extract_z3_proof.py problem.smt2 --full-proof --check-original-assertions --fast-check
wsl -e bash -c '~/z3checker/checker --check-original-assertions proof.json'
```

The document field `"check_original_assertions": true` and native CLI flag
remain compatible, but neither changes the `def-axiom` policy nor adds a
membership requirement to it. The native flag additionally rejects legacy
equational documents, which have no original-input policy. A malformed
metadata field is rejected, and document metadata cannot disable the flag.
The caller must supply the actual original assertions; the checker does
not authenticate a JSON input list against an external SMT file.

The source audit followed `mk_clause_def_axiom` and the gate clauses in
`src\smt\smt_internalizer.cpp:1672-1868`, term ITE clauses at `930-953`,
distinct expansion at `551-561`, and the weakening/true cases in
`src\solver\simplifier_solver.cpp:323-332`. The public schemas are
documented in `src\api\z3_api.h:601-634`.
`Z3BooleanNormalForm.forced` proves a clause by propagating the assumption
that all its disjuncts are false; its semantic lemma does not enumerate
assignments or bound gate arity. A shared Boolean frontier gives consistent
abstraction at depth three, even when operands occur at different depths.
One additional level unfolds literal connectives without adding a
frontier entry per literal of a wide gate.
Validated operator declarations distinguish built-ins from uninterpreted
lookalikes. Binary XOR has an explicit `op_xor` tag and standard Boolean
interpretation contract. Bounded Boolean equivalence remains a fallback
for formulas within a 128-Boolean-node budget; large unsupported theory
axioms do not trigger unbounded normal-form work.

The audit also found forms needing more than propositional reasoning.
Distinct expansion is now checked by the semantic embedding below.
Remaining unsupported forms include BV `carry`/`xor3` gates
(`src\smt\theory_bv.cpp:1052-1101`), quasi-macros with fresh else functions
(`src\ast\macros\quasi_macros.cpp:256-340`), quantified Horn transformations,
and temporary clauses (`src\smt\smt_context.cpp:3463`). An unsupported
instance is an obligation, not silently accepted because of its rule tag.

#### Initial checked-policy calibration (2026-10-15, before distinct support)

The paired run rechecked the same 156 successfully exported certificates
from the existing seed-42, 100-QF_UF/100-QF_AX manifest, without regenerating
proofs. Both binaries used 32 workers and a 10-second per-proof limit:

| Logic | Policy | ACCEPT | PARTIAL | Checker timeout | Not exported |
|---|---|---:|---:|---:|---:|
| QF_UF | Previous trusted axioms | 56 | 0 | 1 | 43 |
| QF_UF | Independently checked axioms | 54 | 2 | 1 | 43 |
| QF_AX | Previous trusted axioms | 79 | 3 | 17 | 1 |
| QF_AX | Independently checked axioms | 79 | 3 | 17 | 1 |

There were no rejects or checker errors. The two formerly accepted UF
proofs (`QF_UF_001`, `QF_UF_015`) now correctly retain a `distinct`
expansion obligation rather than relying on the rule's name. The existing
UF timeout is `QF_UF_094`. The three AX obligations are the previously
documented unsupported rewrites, not new axiom obligations.

A separate axiom-only calibration retained all 11,416 `def-axiom` leaves
from all 156 exports, pruned unused expressions, and appended an asserted
false root solely to exercise every leaf through the native document
checker. This is an axiom-coverage measurement, **not** an additional set
of certified input refutations. It checked 11,413 leaves, with three
explicit obligations and no timeouts, rejects, or errors. The unsupported
leaves are the actual `distinct`-to-pairwise-disequality expansions at
arities 9, 209, and 7 in the three UF certificates above. No `intro-def`
nodes occur in this corpus; fresh Skolem definition witnesses are
additionally covered by ground/quantified regressions.

The archived jobs, per-proof outcomes, binary provenance, and pruned
axiom-only certificates are in
`C:\smtlib-benchmarks\proof_check_array_rewrites_20261015_0815\defaxiom-policy`.
The previous/final native SHA-256 hashes are
`d06d634b447037eeb9a336b1c03efb5d050e9802d4784c095b9e6c8345d86513`
and `b881a4aeca6db0baf20fb43e2afe8718d117c9d59d9568493f4d1cabcf4070c6`.
All checker verification conditions, the F* regression module, and the
56-test Python/exporter/native suite pass. Regressions include wide
compound Tseitin gates, XOR and Boolean/term ITEs, both Boolean definition
clause orders, ground and quantified Skolem witnesses, missing guards,
conflicts/cycles, final input freshness, and exact `asserted` membership
in both CLI modes.

### Verified n-ary distinct expansion

`Z3BasicExprTheory.fst` defines `distinct_from` and `distinct_values` as
pairwise inequality over arbitrary semantic values, and proves their
agreement with the existing executable `all_distinct` for equality types.
The general predicate is important: array-valued semantic objects contain
functions and do not have decidable F* equality. No assumption that two
different syntax nodes denote different values is made.

`Z3DistinctAst.fst` adds typed native declarations, constructors,
recognizers, and the exact expansion from
`src\ast\ast.cpp:2584-2602`. Zero or one argument expands to `true`;
two arguments expand to `not (= a b)`; larger arities expand to the flat
conjunction of every pair `i < j`, in source order. Arguments must have
one common sort, including Boolean and array sorts. Repeated arguments
are allowed and correctly make the corresponding disequality false.

`Z3DistinctEmbed.fst` provides `apply_lemma_distinct`, proves that its
synthesized expansion has the same denotation as the original operator,
and derives both generated `def-axiom` clauses:

```text
(or (not (distinct args...)) expansion)
(or (distinct args...) (not expansion))
```

Swapped disjuncts and the binary case's simplified double negation are
recognized. The proof uses only the standard interpretation contract
for `distinct`, plus the existing Boolean/equality contracts; it does
not assume the generated clauses true. `Z3Definitions.tautology` invokes
these rules before propositional abstraction, so neither the truth-table
width limit nor the fallback budget limits the operator's arity.
The checker matches the complete canonical pair list, not arbitrary
subsets or duplicate/mismatched pairs.

The exporter and JSON decoder use the new native `op_distinct` tag.
Full declarations, homogeneous argument sorts, arity, and empty integer
parameters are validated. An uninterpreted lookalike is not promoted
based only on its name. Older documents with an untagged `distinct`
declaration need re-exporting with the updated exporter.

The paired evaluation used the same archived proof DAGs and limits as
above. For five affected certificates, nine operator annotations were
migrated only after matching actual `Z3_OP_DISTINCT` declarations in the
checksum-verified original parsed inputs, including their complete sort
signatures. Ambiguous uninterpreted lookalikes are rejected by the migration;
all other JSON fields and proof DAG nodes are checked unchanged.

| Logic | Before distinct rules: ACCEPT / PARTIAL / timeout | After: ACCEPT / PARTIAL / timeout |
|---|---:|---:|
| QF_UF (57 exports) | 54 / 2 / 1 | 56 / 0 / 1 |
| QF_AX (99 exports) | 79 / 3 / 17 | 79 / 3 / 17 |

Both newly accepted UF proofs now have zero pending obligations. The
axiom-only calibration checks **all 11,416 leaves in all 156 exports with
zero obligations**, including the three previously unsupported `distinct`
expansions. This does not certify the full proofs that still exceed the
10-second limit. The remaining three AX obligations are unrelated rewrites.
There are no new rejects, errors, or axiom-only timeouts.

Jobs, authenticated tag migrations, results, and binary provenance are
archived at
`C:\smtlib-benchmarks\proof_check_array_rewrites_20261015_0815\distinct-extension`.
The previous/final native SHA-256 hashes are
`b881a4aeca6db0baf20fb43e2afe8718d117c9d59d9568493f4d1cabcf4070c6`
and `b4b430fe820940b03523f2e8ed017ac8c8a952542f5c08e30f6df141e874b593`.
All theory/embedding/kernel verification conditions and the executable F*
regression module pass. The 60-test Python/exporter/native suite includes
actual generated distinct proofs, an expansion-derived refutation,
arities 0/1/2/3/9/209, Boolean and array arguments, and rejection or explicit
obligations for malformed declarations, spoofed operators, wrong polarity,
and missing/duplicated/substituted pairs.

### Accumulated definition introductions and final freshness

`intro-def` and `apply-def` are checked rules, including their older
`{"kind":"trusted","rule":...}` encodings. The checker first accumulates
all explicit definition introductions and supported `def-axiom` definition
witnesses, checks the DAG using their
expanded expressions, and **only after checking the closed false root**
checks that none of the introduced function declarations occurs anywhere
in any original input assertion. The final pass includes unused input
assertions, nested terms, and quantifier bodies; it compares entire
function declarations, not textual names, so genuine overloads remain
distinct. A failed freshness check returns `REJECT`, even when ordinary
inference checking completed successfully. This also applies in strict
original-assertion mode.

`Z3Definitions.fst` supports constant definitions, universally quantified
function definitions, Boolean naming clauses (including positive-only
definitions), and the two guarded equalities defining a term ITE.
The function's arguments must be distinct bound variables covering the
definition's parameters; parameter permutations and nested binders are
supported. Equations follow Z3's `expression = name` convention; the
opposite orientation is also recognized when only that side is an
eligible defining head. Boolean/ITE definitions may quantify their
conjuncts separately, as `defined_names.cpp` does.

For `def-axiom`, supported witnesses are defining equations, complete
Boolean/term-ITE definition pairs, and two separate, complementary
guarded equalities defining the same fresh term. The pair may be
universally quantified. A lone guarded equality does not introduce a
definition or establish an arbitrary axiom. Already-checked tautologies
are not treated as introductions, so ordinary Tseitin operands do not
acquire an artificial freshness requirement.

Identical repeated introductions are idempotent. Conflicting definitions,
recursive dependency cycles, ill-sorted or unbound parameters, invalid
defining clauses, and introductions with premises are rejected. Forward
dependencies between acyclic definitions are permitted. All proof entries
are checked, including introductions outside the root's dependency cone.

The implementation uses capture-avoiding, de-Bruijn-indexed expansion,
not an additional trusted equality or a runtime solver call. An
`intro-def` fact must become a checked tautology after expansion;
`apply-def` must become a checked equality or Boolean observational
equivalence. Universal closure and guarded ITE equalities have separate
semantic proofs using standard universal-quantifier/ITE interpretation
contracts. `check_fresh_inputs` has a proved refinement: whenever it
succeeds, expansion leaves the complete original assertion list
syntactically unchanged. Thus the checked transformed derivation is a
refutation of those same inputs, without assuming definitions true in an
arbitrary unchanged interpretation.

The native dependency build and executable F* regressions pass, including
capture avoidance, cycle rejection, and freshness under binders. The
52-test Python/exporter/native suite passes, with positive ground and
quantified schemas, actual use of accumulated definitions in a refutation,
and rejection of a fabricated refutation whose original inputs are
satisfiable. An additional regression checks actual NNF-generated
`intro-def` nodes; unrelated arithmetic obligations remain explicit.

This support does not infer missing definitions from premise-free
`rewrite` leaves: the two
archived array naming obligations still require explicit definition
witnesses. General `sk`, `quant-inst`, and other quantified proof rules
have not been newly verified.

### Verified binary commutativity

`Z3Commutativity.fst` checks precisely `(op x y) = (op y x)` with the same
validated declaration on both sides, matching argument sorts, and no
premises. Supported operators are polymorphic equality (`op_eq`), Boolean
`and`/`or`, and `Int` `+`/`*` (`op_plus`/`op_mul`). Equality includes
uninterpreted, array, and Boolean operand sorts. The inference concludes
ordinary equality, never observational equivalence.

`lemma_eq_commutativity` and `lemma_commutativity_step_sound` derive the
result from standard equality/Boolean semantics.
`lemma_add_commutativity`, `lemma_mul_commutativity`, and
`lemma_arithmetic_commutativity` prove the integer cases from standard
integer evaluation, not a caller-supplied commutativity axiom. The generic
model hypothesis requires arithmetic declarations to implement integer
addition or multiplication over the shared `VInt` value representation
(with the existing interpreter's total fallback on non-integer values).
Only structural matching executes in the native checker;
it does not evaluate or multiply input numerals.

The exporter keeps unsupported commutative theories (`Real`, bit-vector
arithmetic, etc.) and non-binary shapes as explicit obligations. A document
that labels an unsupported or malformed step as checked `commutativity`
is rejected; an uninterpreted symbol or spoofed name/tag is not sufficient.

`Z3UnifiedProof.lemma_check_step_sound` covers the common inference
checker; `lemma_check_node_sound` composes it with asserted inputs,
scoped premises, hypothesis discharge, trusted definitions, and explicit rewrite/unsupported
obligations. Both distinguish equality semantics from observational
semantics. The original `proof`, `rproof`, and `oproof` types remain
available to existing standalone/legacy callers, but the full-DAG checker
no longer constructs them. Theory-specific soundness lemmas remain in
their existing modules.

Rebuild once with `fstar\tools\build_ocaml_checker.ps1`. The script now
extracts both checker roots and derives the WSL source paths from the
checkout instead of assuming `C:\z3fstar`. Its optional `-CacheDir`
reuses existing caches while still checking source/dependency freshness.
Focused tests are `Z3ResolutionProofCheckerTests.fst` and
`tools\test_extract_z3_proof.py`; set `Z3_FSTAR_CHECKER` to the native
executable to include the latter's end-to-end tests.

## What this does and does not establish

The semantic theorems are conditional on interpretation contracts, not a
completed end-to-end SMT-LIB soundness theorem. In particular, the existing
global `boolean_model` ranges over untyped environments and needs a
well-sorted-valuation restriction before an inhabitance/model-construction
theorem is possible. The arithmetic report records this remaining formal
foundation gap separately from the executable certificate results.

This executable is only as trustworthy as the F*/Pulse verification that
produced the `.ml` files it links, **plus** the hand-written runtime
shim's faithfulness to the real `Prims`/`FStar_*`/`Pulse_Lib_*` semantics
those `.ml` files assume. The shim is small and was validated by (a)
cross-checking its `ACCEPT`/`REJECT` verdict against genuine `fstar.exe`
verification on real extracted proofs, and (b) exact-integer and oversized
reference regressions against the native checker. It is not itself a formally verified artifact —
unlike `Z3PulseProofCheckerJson.fst` itself, nothing machine-checks that
`prims.ml`'s `pow2`/`FStar_UInt.ml`'s bitvector ops/etc. actually satisfy
the specifications the Pulse-verified code was proved against; this is a
standard (and, for a code-extraction trust chain, unavoidable) gap also
present whenever F*'s own prebuilt `fstar.cmxa` runtime is used instead.
