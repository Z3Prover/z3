# LRA Farkas-certificate checker: executable theory, Pulse mirror, real-benchmark parser

## Goal

Extend the Pulse-verified proof-checker work
([`PULSE_PROOF_CHECKER_REPORT.md`](PULSE_PROOF_CHECKER_REPORT.md)) to a
theory `proof_checker.cpp` itself only *sometimes* checks: linear real
arithmetic conflicts, `PR_TH_LEMMA` nodes tagged
`("arith" "farkas" c1 .. cn)`. The explicit requirements for this
follow-up:

1. Formalize and prove sound the actual Farkas-certificate check
   `check_arith_literal`/`check_arith_proof` perform
   (`src/ast/proofs/proof_checker.cpp`, lines ~1348-1529).
2. Make the checker **genuinely executable** — a real decision
   procedure that *computes* the refuting constant from a certificate,
   not merely a lemma that checks an externally-supplied witness.
3. Port it to **Pulse** (imperative, heap-mutating, separation-logic
   verified), proven equivalent to the pure specification, continuing
   this project's established pattern.
4. Test against **real QF_LRA SMT-LIB benchmarks**, with the checker
   literally **parsing Z3's own proof-output files** — not
   hand-transcribed certificate data.

All four are now done; see "Files" below for exactly what to read.

## Why this theory is different from everything audited so far

Every other audit in this directory (`*_REWRITER_REPORT.md`,
`PULSE_PROOF_CHECKER_REPORT.md`) formalizes a *recognizer*: "does this
proof/rewrite have the right shape, given its premises". Farkas
certificates are different — `check_arith_proof` does not merely
recognize a shape, it **runs a small decision procedure**: accumulate
a coefficient-weighted sum of normalized literals (`th_rewriter`
collects like terms as it goes) and check that the result is
syntactically a numeral of a sign that contradicts what every
contributing literal asserts. Faithfully formalizing this means the
F* theory itself has to *compute*, not just *check* — hence
`farkas_decide : list cert_entry -> option int`, a real "collect terms,
then decide" algorithm, is the centerpiece of this report, not a
lemma over a pre-supplied witness.

## Architecture

```
 Z3LraFarkasTheory.fst         -- pure F* theory: evaluator, normalization,
   (foundation)                   Farkas soundness, executable farkas_decide
         |
         v
 Z3PulseLraChecker.fst         -- Pulse imperative mirror of farkas_decide,
   (executable checker)           step-counted, proven == farkas_decide
         |
         v
 Z3PulseLraCheckerTests.fst    -- 4 hand-derived certificates (2 real
   (hand-derived fixtures)        benchmarks + 2 synthetic) + 2 rejections
         ^
         |  (cross-checked against)
         |
 tools/parse_farkas.py         -- parses real Z3 proof-output files into
   (the parser)                   cert_entry F* literals
         |
         v
 Z3PulseLraCheckerParsed.fst   -- AUTO-GENERATED: the parser's literal
   (machine-extracted fixtures)   output run through the same checker
```

### `Z3LraFarkasTheory.fst` — the pure theory

* **Term language**: `lin_term` (an unreduced list of `(int, var)`
  monomials plus a constant), mirroring `check_arith_literal`'s own
  `a.mk_add`/`a.mk_mul`-built `sum` exactly — a *build, then collect*
  two-phase shape, not a pre-reduced normal form.
* **`raw_lit`/`normalize`**: models `check_arith_literal`'s branch
  structure precisely — which side gets negated/swapped, and when
  `abs(coeff)` is taken (every relation except `=`) versus the
  coefficient's own sign being trusted unchanged (`=`, uniquely).
  `lemma_normalize_sound` proves this matches the literal's "obvious"
  semantics for every relation/polarity combination **except** one
  documented precondition — see "Findings" below.
* **`cert_entry`/`wf_entry`/`combined_term`/`lemma_combined_sign`**:
  the mathematical content of Farkas' lemma itself — a well-formed,
  all-holding combination evaluates to something `<=0` (or `<0` if a
  strict contributor fired).
* **The executable layer** (new in this report, the bulk of the file):
  `lookup`/`remove_var`/`insert_mono`/`collect` (an association-list
  "collect like terms" accumulator, exactly what `th_rewriter` does
  one monomial at a time), `fold_raw`/`lemma_fold_raw` (an
  unconditional, *total* accumulator fold plus its value-preservation
  proof, parameterized by an explicit environment `rho` rather than a
  universally-quantified one — see "F\* lessons" below), and finally
  **`farkas_decide : list cert_entry -> option int`** — a genuinely
  executable decision procedure requiring *no* externally-supplied
  refuting constant or well-formedness/strictness witness, all of
  which are instead derived from `cert` alone.
* **`lemma_farkas_decide_sound`**: the headline theorem — `Some? (farkas_decide
  cert) /\ all_hold cert rho` implies `False`, for any `rho`.

### `Z3PulseLraChecker.fst` — the Pulse mirror

* **`check_fold_raw`**: a Pulse `fn rec` mirroring `fold_raw`, with a
  heap-allocated step counter (`ref int`) incremented once per
  certificate entry, proven `ensures pure (r == fold_raw cert tbl k
  strict)` (functional correspondence) and `pts_to ctr ('n + length
  cert)` (resource accounting) — i.e. Pulse's own separation-logic
  program logic, not just F*'s type system, verifies every heap
  mutation.
* **`check_farkas_decide`**: the Pulse mirror of `farkas_decide` itself
  (gate on `all_wf_b`, then `check_fold_raw`, then the sign/zero
  check), proven `ensures pure (ok == farkas_decide cert)`.
* **`lemma_check_farkas_decide_sound`**: the end-to-end corollary
  composing the Pulse checker's correctness with
  `lemma_farkas_decide_sound`.

### `tools/parse_farkas.py` — the parser

An ordinary Python preprocessing script (not part of the trusted
formalization — a bug here can only cause F* to *reject* a
certificate it should accept, never a false positive, since
`farkas_decide`'s soundness proof does not depend on this script at
all). Given a captured Z3 proof-output file, it:

1. Tokenizes/parses the S-expression proof term.
2. Collects every `(let ((name val)) ...)` binding into a flat
   alias table (names are unique in Z3's own proof printer output).
3. Locates the `((_ th-lemma arith farkas c1 .. cn) ant1 .. antn
   false)` application node.
4. For each antecedent, **resolves the alias chain** down to its raw
   arithmetic literal: repeatedly peels "proof application → its last
   argument" (for `asserted`/`mp`/`and-elim`/...) and "bound name →
   its definition" steps until a literal relation expression is
   reached.
5. Evaluates each side of the literal as a linear expression
   (recursively resolving any further `let`-bound aliases *inside*
   the arithmetic expression itself, e.g. Z3 printing `10*skoX` as an
   aliased sub-term `?x25`), using exact `Fraction` arithmetic.
6. Applies the **same** `normalize`-with-`is_pos=true` case split
   `Z3LraFarkasTheory.fst` itself uses, to get a normalized
   `(term, strict, is_eq)` atom.
7. **Clears denominators while preserving exact algebraic
   equivalence**: each atom is scaled by its own denominator LCM
   `d_i`; the whole certificate is then uniformly scaled by `D = lcm
   over i of d_i`, giving each entry's final integer coefficient
   `c_i * (D / d_i)` — this is provably just "the original valid
   combination, scaled by the positive constant `D`" (scaling a valid
   Farkas combination by a positive constant preserves validity), not
   an approximation.
8. Emits ready-to-typecheck `cert_entry` F* literals.

Run with:
```
python tools/parse_farkas.py qf_lra_bench/full_polypaver.txt qf_lra_bench/full_sqrt.txt \
       qf_lra_bench/full_synthetic1.txt qf_lra_bench/full_synthetic2.txt
```

### `Z3PulseLraCheckerTests.fst` / `Z3PulseLraCheckerParsed.fst` — the test fixtures

Four certificates, tested twice over (once hand-derived, once
machine-parsed — see "Validation" below):

| # | Certificate | Provenance | Antecedents | Refuting constant |
|---|---|---|---|---|
| 1 | `polypaver` | real QF_LRA benchmark (`polypaver__bench-exp-3d`, chunk 0047), `smt.arith.solver=2` | `skoZ,skoX,skoY>=0`, `skoZ+skoX+skoY<=-14/9` | `14` (scaled ×9) |
| 2 | `sqrt` | real QF_LRA benchmark (`sqrt__1mcosq__7`, chunk 0108), `smt.arith.solver=2` | `skoX>=1/20`, `skoY<=0`, `10skoX-skoY<=0` | `10` (scaled ×20) |
| 3 | `synthetic1` | hand-authored, 3 vars, 4 antecedents | `y+z<=2`,`x+y+z>=4`,`x+z<=2`,`x+y<=2` | `2` |
| 4 | `synthetic2` | hand-authored, 2 vars, 3 antecedents | `2x+3y<=5`,`x>=2`,`y>=1` | `2` |

Plus two deliberately malformed variants confirming correct rejection:
one with a negative coefficient on a non-equality atom (`all_wf_b`
rejects before any folding), one well-formed but with an antecedent
dropped so the variables never fully cancel (`all_zero` fails).

Every certificate above is run through **both** the pure
`farkas_decide` (direct equality assertion against the expected `Some
k`/`None`) and the Pulse `check_farkas_decide` (via a `run_one`/
`run_parsed` harness, confirming the live, heap-mutating program
returns the identical verdict), plus `lemma_farkas_decide_sound`/
`lemma_check_farkas_decide_sound` instantiated concretely to derive
`False` from `all_hold cert rho` for each one.

## Validation: hand-derivation vs. machine parsing agree exactly

The two real-benchmark certificates in `Z3PulseLraCheckerTests.fst`
were originally derived *by hand* (reading the captured proof text and
manually computing the normalized/scaled atoms) in an earlier pass of
this project. Running `tools/parse_farkas.py` on the same captured
proof files (`qf_lra_bench/full_polypaver.txt`,
`qf_lra_bench/full_sqrt.txt`) — independently, mechanically — produced
**term-for-term, coefficient-for-coefficient identical** `cert_entry`
lists (confirmed by direct comparison of the generated output against
the hand-authored file; see `Z3PulseLraCheckerParsed.fst`'s header).
This is a meaningful cross-check in both directions: it confirms the
hand derivation was faithful to the real proof text, *and* it confirms
the parser's alias-resolution/scaling logic is correct, since two
independently-produced encodings of the same real proof node agree
exactly.

The two synthetic certificates were re-derived the same way: the
`.smt2` source files (`qf_lra_bench/synthetic1.smt2`/`synthetic2.smt2`)
were re-run through `z3.exe smt.arith.solver=2` to capture fresh proof
output (`full_synthetic1.txt`/`full_synthetic2.txt`), then parsed —
again producing output identical to the hand-authored fixtures.

## What was formally verified, precisely

1. **`farkas_decide` is a real decision procedure, proven sound with no
   external witness.** Earlier-style "witness-checking" lemmas
   (`lemma_farkas_unsat`, requiring a caller-supplied `k` and a
   caller-supplied proof that it is a refuting constant) are
   superseded by `lemma_farkas_decide_sound`, which derives
   everything — the constant, well-formedness, and the strictness
   flag — from the certificate alone.
2. **The Pulse mirror is a real, heap-mutating program**, not a
   disguised pure function: `check_fold_raw`'s step counter is proven
   to advance by exactly `length cert`, and its final answer is proven
   (via Pulse's own separation-logic VCs, composed with the SMT
   discharge) to equal `fold_raw`'s pure result at every step, for
   every path through the recursion.
3. **The parser's output is independently cross-checked**, not merely
   type-correct: two real benchmark certificates were derived twice,
   by two different methods (hand algebra vs. mechanical parsing),
   and the results agree exactly; two synthetic certificates were
   likewise re-derived from fresh Z3 output and agree with their
   original hand-authored fixtures.
4. **End-to-end**: for every one of the four certificates (both the
   hand-derived and the freshly machine-parsed copies),
   `lemma_farkas_decide_sound cert rho` is instantiated concretely,
   proving no environment `rho` can satisfy all of that certificate's
   literals simultaneously — i.e. each real/synthetic benchmark's
   actual infeasibility is independently re-derived in F*, not merely
   assumed because Z3 said "unsat".

## Findings (genuine gaps in Z3's own proof checker)

These were discovered while formalizing `check_arith_literal`/
`check_arith_proof` and are modeled explicitly as preconditions in
`Z3LraFarkasTheory.fst` (not silently papered over):

1. **`num_params == 1` is unconditionally trusted.** `check_arith_proof`
   only performs any check at all when the proof node's tag is
   literally `("arith" "farkas" ...)`; a bare `("arith")` tag (no
   `"farkas"` parameter) is accepted with zero verification
   (`dump_proof(p); return true;`). Empirically (see `tools/` session
   history), Z3's **modern default** arithmetic engine
   (`smt.arith.solver=6`, `smt/theory_lra.cpp`) essentially *never*
   populates Farkas coefficients on its main simplex-conflict path —
   only the **old** engine (`smt.arith.solver=2`,
   `smt/theory_arith_core.h`) reliably emits genuine, checkable,
   multi-term `farkas` certificates. This means **under Z3's current
   default configuration, real QF_LRA UNSAT results' core arithmetic
   reasoning is essentially never independently re-verified by Z3's
   own proof checker** — this report's checker only has real
   certificates to validate against because `smt.arith.solver=2` was
   explicitly selected when harvesting benchmark data.
2. **Equality-literal orientation is never actually checked.**
   `check_arith_literal`'s `std::swap(a0, a1)` orientation logic (the
   code that picks which side of a relation contributes positively vs.
   negatively) is gated only on `is_ge`/`is_gt`/`is_le`/`is_lt` — never
   on `m.is_eq`. So an equality literal's contribution is *always*
   computed as `coeff*(a0-a1)` regardless of the literal's actual
   polarity. This is sound exactly when the equality is genuinely
   being assumed true (`effective_pos is_pos l`); `Z3LraFarkasTheory.fst`
   makes this an explicit hypothesis of `lemma_normalize_sound`
   (`l.rl == Eqr ==> effective_pos is_pos l`) precisely because the
   real C++ code never verifies it — a hypothetical negated-equality
   antecedent fed through this path would be treated unsoundly. No
   real harvested certificate exercises this path (LRA disequalities
   are handled by case-splitting elsewhere in Z3, not fed directly into
   Farkas combinations), so this is not known to be exploitable in
   practice, but it is a second, independent, unchecked soundness
   precondition, alongside finding 1.

## F\*/Pulse lessons (new this report, for future work in this project)

* **`FStar.Classical.forall_intro (fun rho -> lemma1 rho; lemma2 rho; ...)`
  only generalizes the *last* call's conclusion** — intermediate facts
  established earlier in the closure are silently dropped from the
  resulting `forall` fact. Fix: extract one dedicated helper lemma
  with a single explicit `ensures` capturing everything needed, or
  avoid `forall_intro` by making the quantified variable an *explicit
  function parameter* instead (used throughout `lemma_fold_raw`).
* **A proof body ending in a non-`()` expression** (e.g. a trailing
  `Lemma`-returning call) can fail with "subtyping check failed" even
  when every fact needed is already in context — F* compares the
  declared `ensures` against that last call's *own* type. Fix: always
  end multi-step lemma bodies with an explicit trailing `()`.
* **Tuple-destructuring a recursive function's result inside a
  `Lemma`'s `ensures`/body is poorly handled by F*'s SMT encoding** for
  the recursive-unfolding equality a structural induction needs. Fixed
  by (a) using a **named record type** (`fold_result`) instead of an
  anonymous tuple, and (b) exposing the one-step unfolding fact as its
  **own named lemma** (`lemma_fold_raw_cons`, proved via `assert_norm`)
  rather than relying on ad hoc `assert`s at each call site — this was
  essential not just for the pure proof but for the **Pulse** mirror
  too, since Pulse has no `assert_norm` of its own and must call out
  to a pre-proved F* lemma for this fact.
* **Splitting an "`Option`-returning, well-formedness-interleaved"
  recursive function into an unconditional total fold plus a single
  top-level well-formedness gate** (`fold_raw` vs. `farkas_fold`/
  `farkas_decide`) turns the core value-preservation lemma into a
  *plain* structural induction, avoiding `Option`/`None`-case threading
  through every recursive step.

## Scope and limitations

* **Parser scope**: `tools/parse_farkas.py` only handles the common
  "single `false` conclusion, every antecedent asserted positively"
  shape — every real certificate harvested for this project uses
  exactly this shape (see `Z3LraFarkasTheory.fst`'s module header for
  why `check_arith_proof`'s more general disjunctive-conclusion case
  is out of scope here as well). An antecedent already negated, or a
  disjunctive conclusion with per-disjunct coefficients, raises
  `NotImplementedError` rather than silently mishandling it.
* **No OCaml/C extraction was attempted** — as with the prior Pulse
  report, this is a verified-model exercise within F*/Pulse's own type
  checker; nothing in `src/ast/proofs/proof_checker.cpp` was modified.
* **`alloc`/`free` deprecation warnings**: same documented tradeoff as
  `PULSE_PROOF_CHECKER_REPORT.md` — the self-contained test harnesses
  use the simpler (if `@@deprecated`-flagged) `alloc`/`free` API rather
  than the scoped `with_local`; not a soundness gap in the proved
  specifications, since Pulse's `pts_to`/ownership VCs are still fully
  discharged around every `alloc`/`free` pair.
* **Benchmark coverage**: two real QF_LRA benchmarks (both from the
  PolyPaver/Meti-Tarski collection bundled with the downloaded QF_LRA
  set) were used; richer multi-dozen-term certificates exist in the
  broader benchmark set (`qf_lra_bench/` contains additional `.smt2`
  files not yet run with `smt.arith.solver=2`/parsed) but were not
  pursued further for this report.

## Files

| File | Role |
|---|---|
| [`Z3LraFarkasTheory.fst`](Z3LraFarkasTheory.fst) | Pure theory: evaluator, normalization, Farkas soundness, executable `farkas_decide` |
| [`Z3PulseLraChecker.fst`](Z3PulseLraChecker.fst) | Pulse imperative mirror of `farkas_decide`, proven equivalent |
| [`Z3PulseLraCheckerTests.fst`](Z3PulseLraCheckerTests.fst) | 4 hand-derived certificates (2 real benchmarks + 2 synthetic) + 2 rejection tests |
| [`tools/parse_farkas.py`](tools/parse_farkas.py) | Parses real Z3 proof-output files into `cert_entry` F* literals |
| [`Z3PulseLraCheckerParsed.fst`](Z3PulseLraCheckerParsed.fst) | Auto-generated: the parser's literal output, run through the same checker |
| `qf_lra_bench/` | Captured real Z3 proof-output files (`full_*.txt`) and their source `.smt2` benchmarks/synthetics |

All five `.fst` files type-check cleanly with the standard toolchain
invocation (`fstar.exe --smt <z3 4.13.3 binary> <File>.fst`), with zero
errors and zero admits; the only diagnostics are the expected
`alloc`/`free` deprecation warnings (consistent with
`PULSE_PROOF_CHECKER_REPORT.md`) and a harmless "no `.checked` file yet"
warning on first run.
