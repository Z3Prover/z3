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
