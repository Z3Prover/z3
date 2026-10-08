# `seq_rewriter.cpp` nested-extract + `mk_seq_index` width audit

## Scope

This audit is a focused follow-up to the broader sequence-rewriter pass in
[`SEQ_REWRITER_REPORT.md`](SEQ_REWRITER_REPORT.md). It covers exactly the two
NFV triage items flagged in `C:\bench\NFV-Oct8.md` as "likely genuine bugs":

- `src/util/zstring.cpp` / `zstring.h` / `src/ast/rewriter/seq_rewriter.cpp`'s
  concrete-string `indexofu` fast path used by `mk_seq_index`.
- The nested-`extract` / nested-`substr` flattening rules in
  `seq_rewriter.cpp::mk_seq_extract`.

Unlike the earlier sequence audit, this pass is intentionally **length-only**:
the suspected `mk_seq_extract` issue is purely about how requested lengths are
composed and clamped, so characters themselves are irrelevant. The new F*
modules are:

- [`Z3SeqRewriterExtract.fst`](Z3SeqRewriterExtract.fst): a natural-number model
  of SMT-LIB extract-length semantics, with one lemma per nested-extract branch.
- [`Z3SeqRewriterIndex.fst`](Z3SeqRewriterIndex.fst): a minimal representability
  audit for the `int`-returning `indexofu` helper versus SMT-LIB's
  arbitrary-precision `seq.indexof`.

Both files were verified with F* `v2026.09.27` and its bundled Z3 `4.15.3`
using:

```text
fstar.exe Z3SeqRewriterExtract.fst --z3rlimit 40
fstar.exe Z3SeqRewriterIndex.fst --z3rlimit 40
```

Both report `Verified module: ... — All verification conditions discharged
successfully`, with no `admit`/`sorry`.

## Source-to-lemma correspondence

### `Z3SeqRewriterExtract.fst`

| C++ source rule | F* lemma(s) |
|---|---|
| `is_suffix` recognizer (`seq_rewriter.cpp:774-783`) | `suffix_exact_len` |
| nested `is_suffix` + `is_suffix` flattening (`seq_rewriter.cpp:1017-1024`) | `suffix_suffix_flatten_len` |
| general numeral nested-extract branch (`seq_rewriter.cpp:1027-1050`) | `nested_numeric_flatten_len`, `zero_offset_covering_shortcut_len` |
| nested `is_prefix` + `is_prefix` flattening (`seq_rewriter.cpp:1053-1056`) | `prefix_prefix_flatten_len` |
| nested outer-`is_prefix` / inner-`is_suffix` flattening (`seq_rewriter.cpp:1058-1064`) | `prefix_of_suffix_flatten_len` |
| nested-`extract` identity branch `extract(extract(x,p,l),0,|x|)` (`seq_rewriter.cpp:1067-1070`) | `nested_extract_identity_len_of_base` |
| nested-`extract` identity branch `extract(extract(x,p,l),0,l)` (`seq_rewriter.cpp:1073-1076`) | `nested_extract_identity_len_of_same_request` |
| nested outer-`is_suffix` / inner numeral branch (`seq_rewriter.cpp:1079-1085`) | `suffix_of_numeric_flatten_len` |
| NFV witness sanity check (`|X|=1, p=0, requested=2, d=1`) | `nfv_witness_semantics` |

### `Z3SeqRewriterIndex.fst`

| C++ source rule | F* lemma(s) |
|---|---|
| `zstring::indexofu` returns exact mathematical index or `-1` in unbounded arithmetic (`src/util/zstring.cpp:198-210`) | `indexofu_not_found_spec`, `indexofu_found_spec` |
| `mk_seq_index`'s concrete-string fast path is correct only when the true index fits signed 32-bit (`seq_rewriter.cpp:1637-1647`) | `indexofu_correct_when_in_range` |
| removing the signed-32-bit bound breaks exactness (`int` width mismatch) | `indexofu_width_mismatch_counterexample` |

## What was verified, from first principles

- **Exact SMT-LIB extract length semantics.**  
  The core definition
  `extract_result_len(|s|, offset, req) = 0` when `offset >= |s|`, otherwise
  `min(req, |s| - offset)`, is the whole semantic model. Every branch proof is
  just arithmetic over that definition.

- **Every actual nested-extract flattening branch in `mk_seq_extract` is
  length-sound, including overlong inner requests.**  
  The general numeral composition branch
  (`nested_numeric_flatten_len`) proves the standard law
  `extract(extract(x,p1,l1), p2, l2) = extract(x, p1+p2, min(l1-p2,l2))`
  under exactly the C++ guard `p2 <= l1`, with **no extra assumption**
  `l1 <= |x|-p1`. So the already-known general composition rule remains valid
  even when the inner request is overlong.

- **The supposedly suspicious suffix branch is still sound after clamping.**  
  `suffix_of_numeric_flatten_len` formalizes
  `extract(extract(x,p1,l1), p2, |extract(...)|-p2) ->
   extract(x, p1+p2, l1-p2)`.
  Even if `l1` is larger than the available suffix of `x`, the flattened outer
  `extract` clamps against `|x|-(p1+p2)`, recovering exactly the true final
  length.

- **The prefix/suffix syntactic special cases are also sound.**  
  `suffix_suffix_flatten_len`, `prefix_prefix_flatten_len`, and
  `prefix_of_suffix_flatten_len` show that each of the recognizer-based
  shortcuts computes the same final clamped length as the nested SMT-LIB
  semantics.

- **Both nested-`extract` identity rewrites are exact.**  
  The two branches reducing
  `extract(extract(x,p,l),0,|x|)` and `extract(extract(x,p,l),0,l)` back to the
  inner extract preserve length unconditionally.

- **The external NFV witness does not even reach a flattening branch.**  
  For `|X| = 1`, inner `extract(X, 0, 2)`, outer
  `extract(inner, 0, |inner|-1)`:
  - the inner extract is **not** `is_suffix` (that helper requires a
    **positive** offset, `seq_rewriter.cpp:778-782`);
  - the inner extract is **not** `is_prefix` (that helper requires the length
    expression to be syntactically `len(base) - positive_constant`,
    `seq_rewriter.cpp:785-793`, whereas `2` is just a numeral);
  - the general numeral-composition branch does **not** fire because the outer
    length is symbolic (`len(inner)-1`), not a numeral;
  - after the nested special-case checks fail, control reaches
    `if (pos == 0 && !constantLen) return BR_FAILED;`
    (`seq_rewriter.cpp:1109-1111`), so no flattening rewrite occurs at all.

- **`indexofu` really does have a type-width mismatch.**  
  SMT-LIB's `seq.indexof` result is an arbitrary-precision integer. The concrete
  fast path in `mk_seq_index` computes `int idx = s1.indexofu(s2, ...)` and
  then injects that `int` into an unbounded Z3 numeral. The F* lemma
  `indexofu_correct_when_in_range` proves exactness when the true index is
  `< 2^31`, and `indexofu_width_mismatch_counterexample` proves that the naive
  unconditional claim is false: `2^31` itself cannot be represented by signed
  32-bit `int`.

## Verdict on the two NFV claims

### 1. `z3#11098` (`zstring::indexofu` / `mk_seq_index`)

**Confirmed.**  
This is a real semantic mismatch between the C++ implementation type and the
SMT-LIB result type. The search algorithm may find a correct mathematical match
position `k`, but the concrete rewrite path can only return it exactly when
`k < 2147483648`. The counterexample is schematic but genuine: a concrete
string whose first match is at position `2^31` has a valid SMT-LIB result that
no signed 32-bit C++ `int` can equal.

### 2. `z3#11080` (`mk_seq_extract` overlong prefix/suffix flattening)

**Refuted.**  
After checking the full function branch-by-branch and then proving each actual
nested-extract flattening rule in F*, I found **no unsound branch**. The
reported witness `|X|=1, p=0, requested=2, d=1` is especially instructive: it
does not satisfy any of the recognizer-based flattening guards, and the general
numeral branch is inapplicable because the outer requested length is symbolic.
So the witness does not trigger a flattening rewrite in the real C++ control
flow. Moreover, the branch that looked most suspicious on paper
(`suffix_of_numeric_flatten_len`) is provably sound once the outer flattened
extract's own clamping is accounted for.

## Out of scope

- Character-by-character equality/search correctness for `indexofu`. This audit
  isolates the **width** issue only; the solver-level arbitrary-precision
  `indexof` semantics already live in [`Z3SeqIndexOf.fst`](Z3SeqIndexOf.fst).
- Non-nested `mk_seq_extract` rules already covered in
  [`SEQ_REWRITER_REPORT.md`](SEQ_REWRITER_REPORT.md).
- Concat-boundary decomposition and segment walking inside `mk_seq_extract`
  (still the main remaining hard part of that function).
- C++ implementation-defined details of out-of-range `unsigned -> int`
  conversion. The only property needed here is simpler: exact agreement with the
  SMT-LIB integer result is impossible once the true index exceeds signed
  32-bit range.

## Files

| File | Subject | Lemma count | Verified |
|---|---|---|---|
| `Z3SeqRewriterExtract.fst` | `mk_seq_extract` nested-flattening branches | 10 | ✅ |
| `Z3SeqRewriterIndex.fst` | `indexofu` / `mk_seq_index` width mismatch | 4 | ✅ |

## Conclusion

This follow-up audit splits the two NFV candidates cleanly:

- **Confirmed genuine bug:** `mk_seq_index`'s concrete-string fast path is only
  conditionally correct because `zstring::indexofu` returns signed 32-bit `int`
  while SMT-LIB `seq.indexof` is unbounded.
- **False alarm:** the claimed overlong nested-`extract` flattening bug in
  `mk_seq_extract` does not hold up. The cited witness does not reach a
  flattening branch, and every real nested-`extract` flattening branch in the
  function is length-sound under exact SMT-LIB clamping semantics.
