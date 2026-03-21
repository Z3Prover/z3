# [nseq] Soundness bug: conflicting regex memberships not detected (norn-benchmark-9f)

**Labels**: bug, c3, nseq, soundness

## Summary

The nseq solver returns `sat` for a formula asserting that a non-empty string belongs
simultaneously to two disjoint regular languages. The correct answer is `unsat`.

## Affected benchmark

| File | seq verdict | nseq verdict |
|------|-------------|--------------|
| `norn-benchmark-9f.smt2` | unsat | **sat** (WRONG) |

Data from: https://github.com/Z3Prover/z3/discussions/9071

## Reproducing example

```smt2
; norn-benchmark-9f.smt2 — EXPECTED: unsat, nseq returns: sat
(set-logic QF_S)
(declare-fun var_0 () String)
(assert (str.in.re var_0 (re.* (re.range "a" "u"))))
(assert (str.in.re var_0 (re.* (str.to.re "v"))))
(assert (not (= var_0 "")))
(check-sat)
```

The formula asserts:
1. `var_0 ∈ (re.range "a" "u")* ` — all characters in "a"–"u"
2. `var_0 ∈ "v"*` — only the character "v"
3. `var_0 ≠ ""`

Since "v" is not in the range "a"–"u" (the range includes up to 'u', not 'v'),
the intersection of the two languages is `{""}`. Combined with `var_0 ≠ ""`, this is
unsatisfiable.

## Note on syntax

This benchmark uses the old SMT-LIB 2.5 syntax `str.in.re` (with dots) rather than
the SMT-LIB 2.6 syntax `str.in_re` (with underscore). Both are supported by Z3's parser.
The bug may be triggered specifically by the old-style syntax interaction with nseq's
regex handling, or may be a pure logic issue.

## Analysis

The nseq solver handles `str.in_re` constraints by computing the intersection of
multiple regex membership constraints for the same string variable (via the sgraph and
Nielsen graph). The Parikh image pre-check (`seq_parikh.cpp`) should detect that
`(re.range "a" "u")* ∩ "v"*` restricted to non-empty strings is empty, since:
- `"v"*` allows only 'v' characters
- `(re.range "a" "u")*` allows only characters in 'a'..'u'
- 'v' ∉ 'a'..'u' → intersection = `{""}` only

The root cause is likely that the nseq solver does not derive the character-level
disjointness between these two regex languages. The seq solver may use a derivative-based
or automaton intersection approach that detects this.

## Files to investigate

- `src/smt/seq/seq_regex.h` / `seq_regex.cpp` — regex membership processing, pre-check
- `src/smt/seq/seq_parikh.h` / `seq_parikh.cpp` — Parikh image constraint generation
- `src/smt/seq/seq_nielsen.cpp` — membership processing in Nielsen nodes
- `src/smt/theory_nseq.cpp` — `assign_eh` for regex membership
