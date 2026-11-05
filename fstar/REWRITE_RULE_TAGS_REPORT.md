# Tagging and Verifying Z3's Rewrite-Rule Proof Leaves — Coverage Report

See [`README.md`](README.md) for the top-level index of this F*
formal-verification audit series.

> **Status update (post-hoc):** the `th_rewriter_cfg::reduce_app` tagging
> call site described below has since been **reverted from master** — the
> `mk_rewrite(s, t, rule)` overload and `get_rewrite_rule` accessor remain
> in `src/ast/ast.h`/`ast.cpp` (harmless, unused), but ordinary term
> rewrites are no longer tagged by current `z3.exe` builds. The 7 SMT-LIB2
> benchmarks and their captured `(get-proof)` output are kept locally only
> (`fstar/rewrite_rule_bench/`, git-ignored, not in this repository) rather
> than deleted. Everything below describes the point-in-time result that
> was achieved and independently validated while the tagging code was in
> place; it is not a description of current master's behavior.

## Motivation

[`PROOF_REWRITER_REPORT.md`](PROOF_REWRITER_REPORT.md) established that
`rewriter_def.h`'s generic bottom-up rewriting engine assembles proofs
using a fixed, small set of smart constructors, and — crucially — that
**every ordinary term-level simplification** performed by a theory
rewriter (`bool_rewriter`, `arith_rewriter`, `array_rewriter`,
`datatype_rewriter`, `finite_set_rewriter`, `seq_rewriter`, ...) that
doesn't supply its own finer-grained proof falls back to a single,
generic, **unlabeled** `PR_REWRITE` leaf: `mk_rewrite(t0, m_r)`, whose
printed proof term is just `(rewrite (= t0 m_r))` — an opaque "trust me"
node carrying no information about *which* rewrite rule actually fired.

Inspecting `src/ast/rewriter/th_rewriter.cpp`'s `reduce_app` wrapper
(the single chokepoint every theory's `mk_app_core` dispatch passes
through) confirmed this is architectural, not incidental:
`result_pr` is hard-coded to `nullptr` at the top of `reduce_app`, and
no theory's `mk_app_core` signature even has a proof-output parameter
— so, prior to this segment, **no ordinary Boolean/arithmetic/array/
datatype/finite-set/sequence term rewrite could possibly be tagged with
which specific case fired**, even in principle.

This report covers the fix — adding an optional rule-identifying symbol
parameter to `PR_REWRITE` and populating it generically at the
`reduce_app` chokepoint — plus new real benchmarks (one SMT-LIB2 file
per requested theory: Boolean, Arithmetic, Arrays, Datatypes,
FiniteSets, Strings) exercising it, a genuine S-expression parser
extracting the tagged facts from real `(get-proof)` output, and an F*
file (`Z3RewriteRuleTags.fst`) matching each extracted fact against the
specific already-proven lemma (in this project's existing per-theory
rewriter-correctness audits) it is a literal instance of.

## The C++ change

### 1. A parameterized `PR_REWRITE`

`src/ast/ast.h`/`ast.cpp`: added

```cpp
proof * mk_rewrite(expr * s, expr * t, symbol const & rule);
symbol get_rewrite_rule(proof const * p) const;
```

`PR_REWRITE` previously always used a single cached, zero-parameter
`func_decl` (`mk_proof_decl("rewrite", k, 0, m_rewrite_decl)`), so it
had no way to carry extra data. `basic_decl_plugin::mk_func_decl`
already has a generic "does this `basic_op_kind` carry parameters?"
dispatch (used by `PR_TH_LEMMA`/`PR_QUANT_INST`/`PR_HYPER_RESOLVE` to
attach a theory-id/pattern-count/etc. symbol): `PR_REWRITE` was added
as a fourth case there, so `mk_rewrite(s, t, rule)` builds exactly the
same one-argument proof term as before (`(rewrite (= s t))`), but with
`rule` attached as the `func_decl`'s first parameter — printed as
`((_ rewrite rule) (= s t))`, a backward-compatible extension (an
untagged `mk_rewrite(s, t)` call, and every existing proof consumer
that doesn't look at decl parameters, is completely unaffected).
`get_rewrite_rule` is the read-side accessor, returning `symbol::null`
for an untagged (or non-`PR_REWRITE`) proof.

`proof_checker::check1_basic`'s `PR_REWRITE` case was **not** changed:
it already accepts any well-formed `(s = t)` fact regardless of decl
parameters, so tagged and untagged rewrite leaves are both still
accepted exactly as before — the tag is a strictly additive annotation,
not a new precondition the checker enforces.

### 2. Generic tagging at the one real chokepoint

`src/ast/rewriter/th_rewriter.cpp`'s `reduce_app`: added a small
`tag_rewrite(f, num, args, result)` helper, called at the point(s)
where `st == BR_DONE` and no finer-grained `result_pr` has already been
supplied by a sub-dispatch (`push_ite`/`pull_ite`/the partial-eq
fallback). It builds the tag as `"<family-name>:<decl-name>"` (e.g.
`"basic:and"`, `"arith:+"`, `"array:select"`, `"datatype:hd"`,
`"finite_set:set.union"`, `"seq:str.++"`) from the function symbol `f`
being rewritten, and calls the new `mk_rewrite(old_term, result, tag)`
instead of leaving `result_pr` null (`rewriter_def.h`'s fallback path
then picks up this now-tagged proof instead of synthesizing its own
untagged one, since it only falls back to an untagged `mk_rewrite` when
`m_pr` is still null).

This is a deliberately modest, uniform tag — "which theory + which top
symbol was being simplified" — rather than a precise per-internal-case
label (e.g. it cannot by itself distinguish `bool_rewriter`'s seven
different `mk_and_core` sub-cases). That precision gap is intentional:
achieving finer-grained tags would require threading a proof-output
parameter through every theory's `mk_app_core` signature individually
(dozens of files), which is out of scope for this segment; the chosen
design gets a real, non-trivial amount of information (confirmed below
to be enough to identify a *specific* matching lemma in every one of
the 6 requested theories) with a two-function, single-file change.

### Verification that this doesn't regress anything

- `cmake`+`ninja` rebuild of `shell`/`test-z3`: clean.
- `test-z3.exe /a`: **112/112 unit tests still pass**, unchanged.
- Live `(get-proof)` runs (see below) confirm tagged proofs are
  produced and are structurally identical to the previous untagged
  ones except for the added parameter.

## The benchmarks

`fstar/rewrite_rule_bench/` (new): one SMT-LIB2 file per requested
theory, each `(set-option :produce-proofs true)` and asserting the
negation of a simple true equation specific to that theory, run
through the *rebuilt* `z3.exe` to capture `(get-proof)` output
(`full_<name>.txt`):

| File | Theory | Assertion | Tag observed |
|---|---|---|---|
| `boolean.smt2` | Boolean | `(and p (not p)) = false` | `basic:and` |
| `arithmetic.smt2` | Arithmetic | `(div a 1) = a` | `arith:div` |
| `arrays.smt2` | Arrays | `(select (store a i v) i) = v` | `array:select` |
| `datatypes.smt2` | Datatypes | `(hd (cons x l)) = x` | `datatype:hd` |
| `finitesets.smt2` | FiniteSets | `(set.union s (as set.empty (FiniteSet Int))) = s` | `finite_set:set.union` |
| `strings.smt2` | Strings | `(str.++ "" s) = s` | `seq:str.++` |
| `arithmetic_poly_gap.smt2` (bonus) | Arithmetic | `(+ (* 2 x) (* 3 x)) = (* 5 x)` | `arith:+` (**documented gap**, see below) |

Every file also incidentally exercises `basic:=` (reflexivity, `(= e
e) = true`) and `basic:not` (`(not true) = false`), since the
generic `th_rewriter` simplifies the asserted negated-equality's
Boolean skeleton the same way regardless of theory.

(An initial attempt at a second arithmetic benchmark,
`(/ a a) = 1` requiring `a <> 0`, was found to be handled entirely by
the arithmetic *theory solver* (`th-lemma arith`/`triangle-eq`), not
the rewriter at all — no `PR_REWRITE` leaf of any kind is produced for
it. This is itself informative: it shows the new tag can only report
on rewrites that really do flow through `th_rewriter`'s `reduce_app`,
not on facts established by other parts of the solver, which is an
expected scope boundary, not a bug.)

## The parser

`fstar/tools/parse_rewrite_tags.py` (new): a genuine S-expression
tokenizer + recursive-descent parser (not a regex hack, continuing this
project's established discipline from `tools/parse_farkas.py`) that:

1. Parses the whole proof-output file into one or more top-level
   S-expressions.
2. Builds a flat `let`-alias table (`collect_let_defs`) from every
   `(let ((name val) ...) body)` binding in the file.
3. Scans the parsed tree for every occurrence of the pattern `((_
   rewrite <tag>) <fact>)` (`is_tagged_rewrite_head`).
4. Resolves `<fact>` through the alias table if it is itself just a
   `let`-bound name rather than an inline `(= lhs rhs)` (`resolve_fact`)
   — needed because Z3's proof printer shares repeated sub-proofs via
   `let`, so a tagged rewrite's argument is frequently a bare symbol.
5. Recursively resolves *any* alias appearing anywhere inside `lhs`/
   `rhs` themselves (`resolve_term`) — needed because term-level
   sharing (e.g. `strings.smt2`'s `(str.++ "" s)` is itself only
   introduced via a `let`) is independent of, and can be nested inside,
   fact-level sharing.

Run on all 7 proof files, the parser's output was:

```
=== full_boolean.txt ===
  [basic:and]  (and p (not p))  =  false
  [basic:=]  (= false false)  =  true
  [basic:not]  (not true)  =  false

=== full_arithmetic.txt ===
  [arith:div]  (div a 1)  =  a
  [basic:=]  (= a a)  =  true
  [basic:not]  (not true)  =  false

=== full_arrays.txt ===
  [array:select]  (select (store a i v) i)  =  v
  [basic:=]  (= v v)  =  true
  [basic:not]  (not true)  =  false

=== full_datatypes.txt ===
  [datatype:hd]  (hd (cons x l))  =  x
  [basic:=]  (= x x)  =  true
  [basic:not]  (not true)  =  false

=== full_finitesets.txt ===
  [finite_set:set.union]  (set.union s (as set.empty (FiniteSet Int)))  =  s
  [basic:=]  (= s s)  =  true
  [basic:not]  (not true)  =  false

=== full_strings.txt ===
  [basic:not]  (not true)  =  false
  [seq:str.++]  (str.++ "" s)  =  s

=== full_arithmetic_poly_gap.txt ===
  [arith:+]  (+ (* 2 x) (* 3 x))  =  (* 5 x)
  [basic:=]  (= (* 5 x) (* 5 x))  =  true
  [basic:not]  (not true)  =  false
```

Every extracted triple matches, term-for-term, the specific rewrite the
corresponding benchmark was designed to exercise.

## The F* matching

`Z3RewriteRuleTags.fst` (new) defines a small `tag_entry` registry
(tag, source file, matching lemma, `Matched`/`Gap` status) and, for
every `Matched` entry, a lemma that re-derives the extracted
`(lhs, rhs)` fact by **calling the pre-existing lemma** from that
theory's own rewriter-correctness audit — for *all* values of the free
symbolic constants, not merely the single instance Z3 happened to
produce:

| Tag | Matched lemma | Module |
|---|---|---|
| `basic:and` | `and_contradiction` | `Z3BoolRewriter.fst` |
| `basic:=` | `eq_refl` | `Z3BoolRewriter.fst` |
| `basic:not` | `not_true` | `Z3BoolRewriter.fst` |
| `arith:div` | `idiv_one` | `Z3ArithRewriter.fst` |
| `array:select` | `lemma_select_store_same` | `Z3ArrayTheory.fst` |
| `datatype:hd` | `lemma_accessor_match` | `Z3DatatypeTheory.fst` |
| `finite_set:set.union` | `lemma_union_empty_r` | `Z3FiniteSetTheory.fst` |
| `seq:str.++` | `lemma_concat_empty_l` | `Z3SeqRewrites.fst` |

All matching modules are referenced by qualified name (no `open`),
since several reuse short identifiers (`select`/`union`/`concat`/...)
for unrelated theories.

Typechecked with F* v2026.09.27 (Windows x64), Z3 4.13.3 as the SMT
backend:

```
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3RewriteRuleTags.fst
```

**Typechecks and discharges all verification conditions with no
`admit`/`assume`/axioms.**

## A genuine, documented gap: `arith:+`

The bonus `arithmetic_poly_gap.smt2` benchmark (`(+ (* 2 x) (* 3 x)) =
(* 5 x)`) was deliberately chosen to test whether the tagging mechanism
could also *find* uncovered rewrites, not just confirm covered ones.
It does: the tag `arith:+` identifies that this simplification is
`poly_rewriter`'s generic monomial-collection machinery
(`cancel_monomials`) — which `Z3ArithRewriter.fst`'s own header comment
already flags explicitly as *"search/algorithm code rather than a
single reusable identity"* and *out of scope* (per
`ARITH_BOOL_REWRITER_REPORT.md`). There is no existing lemma of the
general shape "collecting `n` like monomials with coefficients `c_1,
..., c_n` yields a single monomial with coefficient `sum c_i`" for this
tag to match against. `Z3RewriteRuleTags.fst` proves the one concrete
extracted instance directly (trivial for fixed literal coefficients),
but — as its comment stresses — this is *not* evidence that
`cancel_monomials` is verified in general; it is exactly the kind of
gap this reporting mechanism is designed to surface precisely, rather
than silently treating every `PR_REWRITE` leaf as equally trustworthy.

## What this does and does not establish

- **Does establish**: for the 8 tags actually observed across these 7
  real, rebuilt-`z3.exe`-produced proof traces, each tagged `PR_REWRITE`
  leaf's `(s, t)` equation is a literal instance of a lemma already
  proven (for all values of the free symbolic constants, independent of
  this particular Z3 run) in this project's existing per-theory audits.
- **Does not establish**: that *every* possible tag the new mechanism
  can produce has a matching lemma (the `arith:+` case above is a
  concrete counterexample, found by the mechanism itself); that the
  tag precisely identifies *which internal case* of a theory's
  `mk_app_core` fired (it only identifies the top `family:decl-name`,
  per the scope note above); or that rewrites handled entirely by a
  theory *solver* (as opposed to `th_rewriter`) are tagged at all (the
  `(/ a a) = 1` example above falls outside `reduce_app` entirely).
- **Complements, does not replace**, `PROOF_REWRITER_REPORT.md`'s
  soundness theorem: that report shows *rewriter_def.h's proof-assembly
  logic is sound given sound `PR_REWRITE` leaves*; this report gives a
  reproducible, automatable way to check that a *specific* leaf
  produced by a *specific* real Z3 run really is one of the leaves
  whose soundness is independently established elsewhere, rather than
  an unverified new rewrite that slipped in uncovered.

## Files

| File | Role |
|---|---|
| `Z3RewriteRuleTags.fst` | tag → lemma registry + re-derivation lemmas |
| `tools/parse_rewrite_tags.py` | genuine S-expression extractor for tagged `PR_REWRITE` leaves |
| `rewrite_rule_bench/*.smt2` | the 7 SMT-LIB2 benchmarks (6 requested theories + 1 gap) |
| `rewrite_rule_bench/full_*.txt` | their captured real `(get-proof)` output from the rebuilt `z3.exe` |
| `src/ast/ast.h`/`ast.cpp` | `mk_rewrite(s, t, rule)` / `get_rewrite_rule` (new parameterized `PR_REWRITE`) |
| `src/ast/rewriter/th_rewriter.cpp` | `tag_rewrite` helper + `reduce_app` call sites (new) |

## Summary

Extended Z3's `PR_REWRITE` proof-term kind with an optional rule-name
tag, populated generically at `th_rewriter`'s single `reduce_app`
chokepoint (zero per-theory plumbing, 112/112 unit tests still pass);
built 7 real benchmarks spanning Boolean, Arithmetic, Arrays,
Datatypes, FiniteSets, and Strings; wrote a genuine parser extracting
the tagged facts from real proof output; and matched 8 of 8 observed
tags against this project's existing rewriter-correctness lemmas in
`Z3RewriteRuleTags.fst` (7 fully covered, 1 a documented, genuine gap
in the arithmetic audit's scope that the mechanism itself surfaced).
