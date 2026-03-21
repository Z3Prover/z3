# [nseq] Performance regression: nseq times out on regex + word equation benchmarks

**Labels**: performance, c3, nseq

## Summary

The nseq solver times out (exceeds 5 seconds) on several benchmarks that the seq solver
solves in under 30ms. These represent cases where nseq's Nielsen-graph search either
explores too many branches or does not apply available pruning heuristics effectively.

## Affected benchmarks

| File | seq verdict | seq time | nseq verdict | nseq time |
|------|-------------|----------|--------------|-----------|
| `concat-regex.smt2` | unsat | 0.018s | **unknown** (timeout) | >5s |
| `concat-regex3.smt2` | unsat | 0.024s | **unknown** (timeout) | >5s |
| `loop.smt2` | sat | 0.026s | **unknown** (timeout) | >5s |
| `simple-concat-4.smt2` | sat | 0.028s | **unknown** (timeout) | >5s |
| `all-quantifiers.smt2` | unknown | 0.020s | **unknown** (timeout) | >5s |

Data from: https://github.com/Z3Prover/z3/discussions/9071

## Reproducing examples

```smt2
; concat-regex.smt2 — seq: unsat in 18ms, nseq: TIMEOUT
(set-logic QF_S)
(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun d () String)
(assert (= a (str.++ b c)))
(assert (= b (str.++ d c)))
(assert (str.in.re a (re.+ (re.union (str.to.re "x") (str.to.re "y")))))
(assert (str.in.re c (re.+ (str.to.re "x"))))
(check-sat)
```

Why unsat: `a = b ++ c = d ++ c ++ c`. With `a ∈ (x|y)+` and `c ∈ x+`,
all characters in `a` are 'x' or 'y', but `c` forces all its chars to be 'x'.
The word equation creates constraints that (with the regex) force a contradiction.
The seq solver can prove this quickly, but nseq's iterative deepening DFS exhausts
its depth budget.

```smt2
; loop.smt2 — seq: sat in 26ms, nseq: TIMEOUT
(declare-fun TestC0 () String)
(declare-fun |1 Fill 1| () String)
(declare-fun |1 Fill 0| () String)
(declare-fun |1 Fill 2| () String)
(assert (str.in.re TestC0
           (re.++ (re.* (re.range "\x00" "\xff"))
                  ((_ re.loop 3 3) (re.range "0" "9"))
                  (re.* (re.range "0" "9"))
                  (re.* (re.range "\x00" "\xff")))))
; ... (additional constraints)
(check-sat)
```

```smt2
; simple-concat-4.smt2 — seq: sat in 28ms, nseq: TIMEOUT
; Uses recursive function definition (define-fun-rec) with transducer-style constraints
; and regex membership
(check-sat)
```

## Analysis

### concat-regex and concat-regex3

These benchmarks use word equations `a = b ++ c`, `b = d ++ c` combined with regex
memberships. The seq solver uses a length-based approach or Parikh constraints that
quickly prune the search. The nseq solver's Nielsen graph approach uses iterative
deepening DFS (starting at depth 10, doubling each iteration, up to 6 iterations per
`seq_nielsen.cpp:solve()`). For these formulas:

- The Nielsen graph may generate many extensions at each level (characters from the
  regex alphabet, word splits)
- The Parikh pre-check may not prune these cases effectively because the Parikh
  constraints for `(x|y)+` allow many length values
- The solver exhausts all 6 iterations without finding the contradiction

**Fix proposal**: Improve the pre-check for membership intersection. When all strings
in a word equation are constrained to finite-alphabet regexes (e.g., `(x|y)+ ∩ x+`),
use a more aggressive alphabet-intersection analysis to prune branches early.

### loop.smt2 and simple-concat-4.smt2

These benchmarks involve:
- `re.loop` (counted repetition) for `loop.smt2`
- `define-fun-rec` (recursive function definitions for transducer-style constraints) for `simple-concat-4.smt2`

For `loop.smt2`: the `(_ re.loop 3 3)` constraint requires exactly 3 digits to appear
at a specific position. The nseq solver may not have efficient handling for counted
repetitions in the Parikh constraint generator.

For `simple-concat-4.smt2`: the `define-fun-rec` introduces recursive predicates.
These are handled by `unfold_ho_terms()` in `theory_nseq.cpp`, which iteratively
unfolds the recursive definition. The timeout may be due to slow convergence of the
unfolding or the combination with regex constraints.

### Performance improvement opportunities

1. **Better Parikh stride computation for counted repetitions** (`seq_parikh.cpp`):
   `(_ re.loop N N)` has stride 0 and min_len = N * char_len. Ensure this is handled.

2. **Alphabet intersection pre-pruning** in the Nielsen graph: before generating all
   possible character extensions, check if the intersection of the alphabets of all
   regex constraints on a variable is consistent with the required character.

3. **Increase Nielsen DFS depth budget adaptively** or use a BFS strategy for small
   alphabets.

4. **Cache Parikh constraints** across Nielsen nodes that share the same membership constraints.

## Files to investigate

- `src/smt/seq/seq_nielsen.cpp` — `solve()`, `generate_extensions()`, depth budget
- `src/smt/seq/seq_parikh.cpp` — `compute_length_stride()` for `re.loop`, constraint generation
- `src/smt/seq/seq_regex.cpp` — alphabet-intersection analysis
- `src/smt/theory_nseq.cpp` — `unfold_ho_terms()` convergence for recursive definitions
