# Standalone OCaml proof-checker executable

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
| `prims.ml` | `Prims.int`/`bool`/`string`/`list`/`nat`/`pos` as direct aliases to OCaml's own primitive types (`type nonrec int = int`, etc. — `type int = int` alone is rejected by OCaml as a "cyclic type abbreviation"); `int_zero`/`int_one`/`of_int`/`not`/`pow2` |
| `fStar_Pervasives_Native.ml` | `option` aliased to OCaml's native `option` (`type nonrec 'a option = 'a option = None | Some of 'a`); `fst`/`snd` |
| `fStar_List_Tot_Base.ml` | `length`/`rev`/`append`/`op_At`/`hd`/`mem`/`index`, thin wrappers over `Stdlib.List` |
| `fStar_Char.ml` | `char = Prims.int` (a Unicode codepoint, since extracted code pattern-matches character literals as raw integer literals, e.g. `45` for `'-'`); `int_of_char`/`u32_of_char` as identity |
| `fStar_UInt32.ml` | `t = Prims.int`; `v` as identity |
| `fStar_UInt.ml` | Fixed-width modular bitvector arithmetic (`logand`/`logor`/`logxor`/`lognot`/`add_mod`/`sub_mod`/`mul_mod`/`udiv`/`mod1`/`shift_left`/`shift_right`/`rotate_left`/`rotate_right`/`zero_extend`/`ones`/`to_uint_t`) via native bitwise ops masked to `(1 lsl n) - 1` |
| `fStar_String.ml` | `strlen`/`list_of_string`/`string_of_list`, byte-wise via `Stdlib.String`/`Stdlib.Char` (sufficient: the JSON proof format is pure ASCII) |
| `fStar_FunctionalExtensionality.ml` | `restricted_t` as a plain function-type alias (type-level only; never invoked at runtime by this checker) |
| `pulse_Lib_Reference.ml` | `ref`/`alloc`/`read`/`write` over a native OCaml `ref`, matching the exact (ghost-argument-padded) call shapes the extracted code uses: `alloc () v`, `read r () ()`, `write r v` |
| `pulse_Lib_Dv.ml` | `unreachable () = Stdlib.failwith "..."` |
| `main.ml` | CLI entry point: reads JSON from stdin (no args) or a file (one arg), calls `Z3PulseProofCheckerJson.check_proof_json`, prints `ACCEPT`/`REJECT`, exits `0`/`1`/`2` |

**Known limitation**: `Prims.int` is a native 63-bit OCaml `int`, not an
arbitrary-precision bignum (unlike F*'s own `fstar.cmxa`, which uses
Zarith). This was a deliberate, necessary choice — the extracted code
applies native `+`/`-`/`*` operators directly to `Prims.int`-typed values,
which only type-checks if `Prims.int` really is OCaml's `int` — and is
harmless for this checker's actual inputs (proof-node/sort/decl counts,
small bit-vector widths), but would need revisiting (e.g. `Zarith.t`) if
ever applied to genuinely huge integers or wide (>63-bit) bit-vectors.

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
   executable with `ocamlfind ocamlopt <all files in order> -o checker`.
   No opam packages beyond the compiler itself are required.

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

## Full ground refutations (`--full-proof`)

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
The new path is ground-only: quantified/free-variable expressions are
rejected rather than silently treated as ground terms.

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
checked successes. These results remain relative to the default def-axiom
trust policy, not independent validation of those definitions.

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
All `ACCEPT` results remain conditional on the default trusted
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
naming/Skolemization needs model-extension and freshness witnesses and
remains an explicit obligation, as do unverified NNF steps. Non-Boolean
observational equalities and quantified expressions remain outside this
ground checker.
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
theory leaves retain their original obligation. The default `def-axiom`
trust policy is unchanged.

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

All 177 quantified exports are rejected by the ground-only decoder;
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

`def-axiom` is a trusted, premise-free ordinary Boolean leaf by default;
it contributes zero pending obligations. This trusts Z3's generated
definitions, rather than independently proving their validity. The
soundness theorem retains an explicit truth hypothesis for these leaves.
Ordinary `asserted` leaves always require exact membership in the document's
original assertions.

To additionally require each **entire def-axiom conclusion** to match an
original assertion:

```powershell
python fstar\tools\extract_z3_proof.py problem.smt2 --full-proof --check-original-assertions --fast-check
wsl -e bash -c '~/z3checker/checker --check-original-assertions proof.json'
```

The document field `"check_original_assertions": true` enables the same
policy; omission or `false` selects default trust. The native CLI flag
cannot be disabled by document metadata. Strict checking applies even to
older `{"kind":"trusted","rule":"def-axiom",...}` encodings. It rejects
typical Tseitin clauses that are generated rather than supplied as input;
it does not attempt to map those clauses back to parts of assertions.
Membership is structural, not logical equivalence. The caller must supply
the actual original assertions; the checker does not authenticate the
document's input list against an external SMT file. The strict native flag
rejects legacy equational documents, which have no original-input policy.

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

This executable is only as trustworthy as the F*/Pulse verification that
produced the `.ml` files it links, **plus** the hand-written runtime
shim's faithfulness to the real `Prims`/`FStar_*`/`Pulse_Lib_*` semantics
those `.ml` files assume. The shim is small and was validated by (a)
cross-checking its `ACCEPT`/`REJECT` verdict against genuine `fstar.exe`
verification on real extracted proofs, and (b) the documented 63-bit
integer-width limitation. It is not itself a formally verified artifact —
unlike `Z3PulseProofCheckerJson.fst` itself, nothing machine-checks that
`prims.ml`'s `pow2`/`FStar_UInt.ml`'s bitvector ops/etc. actually satisfy
the specifications the Pulse-verified code was proved against; this is a
standard (and, for a code-extraction trust chain, unavoidable) gap also
present whenever F*'s own prebuilt `fstar.cmxa` runtime is used instead.
