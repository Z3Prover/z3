# JSON-based Pulse proof checker interface

## Motivation

`tools/extract_z3_proof.py` originally converted a real Z3 proof object into
one bespoke `.fst` **source file** per benchmark: every sort/decl/expr/proof
node became its own top-level `let srt_N`/`fd_N`/`e_N`/`p_N` binding, and the
file also `open`ed the full checker dependency stack
(`Z3AstTheory`/`Z3ValueTheory`/`Z3ProofTheory`/`Z3InterpretedProofChecker`/
`Z3PatternMatchedProofChecker`/`Z3PulseProofChecker`). Every single proof
therefore forced `fstar.exe` to re-elaborate that whole stack (modulo
`.checked`-file caching of the *unchanged* dependencies) plus a fresh,
proof-sized ADT term tree written out literally as F* syntax.

This segment adds a second, additive path: the same conversion, but emitted
as a compact **JSON document** (structure-shared via integer array indices,
exactly mirroring the existing per-kind caches the `Converter` class already
maintained) plus a tiny, uniform "instance" `.fst` file that is just one
string literal and one function call into an already-compiled checker
library. The old path is unchanged and still works exactly as before; the
new path is reached via `--json`.

## New modules

- **`Z3ProofJson.fst`** (pure): a from-scratch, fuel-bounded recursive-descent
  JSON parser (`parse_json`) plus a decoder layer
  (`decode_sorts`/`decode_decls`/`decode_exprs`/`decode_proofs`/`decode_doc`/
  `parse_proof_doc`) that rebuilds `Z3AstTheory.fst`'s `sort`/`func_decl`/
  `expr` and `Z3ProofTheory.fst`'s `proof` values from the JSON schema below.
  `check_proof_json_wf (s:string) : bool` is a pure, non-Pulse convenience
  entry point (`parse_proof_doc s` succeeds and the root proof is
  well-formed, i.e. `Some? (fact p)`).

- **`Z3PulseProofCheckerJson.fst`** (Pulse): the imperative entry points
  `run_proof_json`/`check_proof_json`, which parse a JSON string and then run
  the *same*, already-audited `Z3PulseProofChecker.check_proof` traversal
  over the decoded proof (with its own `ref int` node-visit counter, exactly
  as every other caller of that module does). Also three pure corollaries:
  - `lemma_proof_json_sound (s, rho)`: if `s` parses to a document whose root
    proof is well-formed **and** every `Rewrite` leaf matched a verified
    lemma (`all_matched p`), the proof's two sides evaluate equal under
    every environment `rho`.
  - `lemma_proof_json_partial_sound (s, rho)`: the weaker counterpart that
    only requires the document's *unmatched* leaves to be soundly justified
    some other way (`leftover_sound (collect_unmatched p)`).
  - `proof_json_unmatched_count_matches (s)`: cross-checks the document's
    declared `unmatched_count` annotation against a freshly recomputed
    `List.Tot.length (collect_unmatched p)`.

Both modules type-check standalone with `fstar.exe` ("All verification
conditions discharged successfully").

## JSON schema (structure sharing via index arrays)

```
{ "sorts": [...], "decls": [...], "exprs": [...], "proofs": [...],
  "root": <int>, "unmatched_count": <int> }
```

Each of `sorts`/`decls`/`exprs`/`proofs` is an array; the i-th element is
"node i", and every cross-reference is that node's plain integer index into
the relevant array. **A node is listed exactly once**, no matter how many
other nodes reference it — the acyclicity invariant (every reference points
to an *already emitted* element of its array) is guaranteed by construction,
since the Python emitter always converts a child before its parent (the same
invariant the old `let`-binding scheme already relied on). Per-element
shapes:

```
sorts[i]  = {"kind":"base","name":<string>}
          | {"kind":"array","dom":[sort idx,...],"rng":<sort idx>}

decls[i]  = {"name":<string>, "domain":[sort idx,...], "range":<sort idx>,
             "interp": <op tag string> | null, "int_params": [<int>,...]}

exprs[i]  = {"kind":"var","idx":<nat>,"sort":<sort idx>}
          | {"kind":"app","decl":<decl idx>,"args":[expr idx,...]}
          | {"kind":"quant","qk":"forall"|"exists"|"lambda",
             "bound_sorts":[sort idx,...],"qsort":<sort idx>,"body":<expr idx>}

proofs[i] = {"kind":"refl","e":<expr idx>}
          | {"kind":"sym","p":<proof idx>}
          | {"kind":"trans","p1":<proof idx>,"p2":<proof idx>}
          | {"kind":"congr","decl":<decl idx>,"args1":[expr idx,...],
             "args2":[expr idx,...],"prfs":[proof idx,...]}
          | {"kind":"rewrite","s":<expr idx>,"t":<expr idx>}
          | {"kind":"quant_intro","qk":"forall"|"exists",
             "bound_sorts":[sort idx,...],"p":<proof idx>}
```

An unrecognized `interp` tag, `kind` tag, or out-of-range index is a hard
parse failure (`None`) — fail-closed by design, so a typo or a
future/unhandled operator can never silently under-constrain a matcher.

## Python harness changes (`tools/extract_z3_proof.py`)

The existing `Converter` class's `sort()`/`func_decl()`/`true_marker()`/
`expr()`/`proof()`/`opaque_leaf()` methods were extended *additively*: next to
every existing `self.X_lines.append(...)` call that emits one F*
`let`-binding, a matching `self.X_json.append({...})` call emits the
corresponding JSON node, at the same array position (`Converter._idx(ident)`
recovers that position straight from the existing `"<prefix>_N"` identifier
string, so the two representations' numbering is kept in sync by
construction — no separate bookkeeping was introduced). No existing
caching/traversal logic was changed; the old `.fst`-source generation path
is bit-for-bit unchanged.

Two call sites previously built sort syntax inline, with no ident to
reference from JSON: a lambda's array-valued `qsort`, and a `forall`/`exists`
quantifier's literal `(BaseSort "Bool")`. Both now go through a proper
`sort()`/new `mk_array_sort()` call so every sort used anywhere has a real,
indexable JSON node.

New CLI flags:
- `--json`: in addition to the usual `.fst` output, also write:
  - `<out>.json` — the JSON proof document itself, and
  - `<out-without-.fst>Json.fst` — the tiny instance file (just
    `let proof_json : string = "..."` plus an `assert_norm
    (check_proof_json_wf proof_json)` and a Pulse `check_extracted` function
    calling `check_proof_json`).
- `--json-out`/`--json-fst-out` override the two output paths.
- `--check` (pre-existing flag) now shells out to `fstar.exe` on **both**
  the old-style `.fst` and (if `--json` was given) the new JSON-instance
  `.fst`, reporting PASS/FAIL for each independently.

## End-to-end verification performed

Ran the extended harness with `--json --check` on two inputs:

1. The project's built-in example (`not(not(x)) == x` via `Xor` refutation):
   both `Z3ExtractedProofTest.fst` (old style) and
   `Z3ExtractedProofTestJson.fst` (new JSON-instance style) were generated
   and **both independently verified** with `fstar.exe` ("All verification
   conditions discharged successfully" for each).
2. A real benchmark, `rewrite_rule_bench/boolean.smt2`: same result — both
   the old-style `.fst` and the new JSON-instance `.fst` verified
   successfully, and the JSON document round-tripped through
   `Z3ProofJson.fst`'s parser/decoder with **no change** in which `Rewrite`
   leaves matched a verified lemma (the matching log produced by the Python
   harness is identical either way, since both paths share the same
   `Converter` traversal — only the output encoding differs).

(Both generated test files/logs/JSON documents were deleted after
verification; they are throwaway, reproducible outputs of the harness, not
committed artifacts — consistent with this project's existing convention of
not committing generated `Z3ExtractedProofTest*`/ad hoc benchmark scratch
files.)

## What this establishes, and what it does not

- `lemma_proof_json_sound`/`lemma_proof_json_partial_sound` give the exact
  same end-to-end semantic guarantee the old per-proof `.fst` template did
  (`lemma_extracted_proof_wellformed` + `checker_accepts` +
  `lemma_unmatched_count_cross_checked`), now established compositionally
  for a proof that arrives as a JSON **string** rather than hand-spelled F*
  syntax — nothing about the trust model changes; `Z3ProofJson.fst` is just
  a (verified-sound, by the corollaries above) *parser* in front of the same
  already-audited checker.
- The intended "compile once, run many" benefit is **structural**: the
  dependency stack's `.checked` files never need to change from one proof to
  the next, and each new proof now costs F* exactly one string-constant
  elaboration plus one function call, rather than a few hundred individual
  top-level `let`-bindings each needing its own type inference/checking
  pass. As a concrete (if modest, at this benchmark's small size) proxy
  metric: for `boolean.smt2`, the old-style `.fst` was 83 lines / 3983 bytes,
  versus 45 lines / 3442 bytes for the JSON-instance `.fst` (which embeds a
  1084-byte JSON payload as a single string literal) — the gap widens
  linearly with proof size, since the old path's line count grows one line
  per AST/proof node while the new path's instance file stays a fixed 45
  lines regardless of proof size.
- **Not independently re-measured here**: an actual wall-clock compile-time
  comparison with a *warm* `.checked` cache for the shared dependency stack.
  `fstar.exe --cache_checked_modules` in this environment could only
  persist `.checked` files for modules with no further unchecked
  transitive dependency (`Z3AstTheory.fst`, `Z3ProofTheory.fst`,
  `Z3PulseProofChecker.fst`); modules reachable from Pulse's own standard
  library (`Z3ValueTheory.fst`, `Z3InterpretedProofChecker.fst`,
  `Z3PatternMatchedProofChecker.fst`, `Z3ProofJson.fst`,
  `Z3PulseProofCheckerJson.fst`) failed to cache because this ad hoc
  CLI session does not have Pulse's own prebuilt `.checked` library files
  available under `--include`. Reproducing the claimed compile-time win
  with real timings needs a proper project build (a `Makefile`/`fst.config`
  driven incremental build, as real F*/Pulse projects use) rather than
  bare `fstar.exe` invocations in a scratch directory; without a warm
  cache, both the old-style and JSON-instance checks took ~10-11s each on
  `boolean.smt2` (statistically indistinguishable), because *both* were
  dominated by re-elaborating the untouched dependency stack from scratch,
  not by the proof content itself. This is recorded here as an open item,
  not a result.

## Files touched this segment

- `fstar/Z3ProofJson.fst` (new)
- `fstar/Z3PulseProofCheckerJson.fst` (new)
- `fstar/tools/extract_z3_proof.py` (additive JSON emission, `--json` mode)
- `fstar/JSON_PROOF_CHECKER_REPORT.md` (this file, new)
