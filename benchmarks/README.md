# Regex equivalence benchmarks

SMT-LIB2 benchmarks used to evaluate the XOR-based regex bisimulation
introduced in PR #9804. Two top-level subdirectories:

## `regex-equivalence/` — 1528 files

Original benchmark sets from the CAV'26 paper and adjacent work.

| Subdirectory | Files | Description |
|---|---:|---|
| `cade29/`              | 120 | Regex equivalence problems from CADE'29 (inequivalent pairs) |
| `cade29_equiv/`        | 107 | Same source, mutated so the pairs become equivalent |
| `equiv_preserved/`     | 101 | Hand-crafted equivalence-preserving rewrites |
| `mutations/`           | 501 | Mutation-based inequivalence checks from AutomatArk |
| `mutations_equiv/`     | 501 | Same mutations, restricted to ones meant to preserve equivalence |
| `realworld/`           | 100 | Real-world regexes (CSS, HTML, etc.) |
| `realworld_equiv/`     |  98 | Equivalence-preserving rewrites of the above |

Subfolders under `cade29/` and `cade29_equiv/` (`boolean_and_loops`,
`inclusion_equiv`, `parametric`, `regexlib_equiv`) further categorise the
problems by structural shape.

## `hard/` — 342 files

Extracted "hard" subsets, used for focused comparison between master and
the xor branch.

| Subdirectory | Files | Description |
|---|---:|---|
| `master_hard/`   | 291 | Cases where master takes more than a few seconds or times out (with `manifest.csv` recording the source folder of each file) |
| `ba_ab_param/`   |  50 | Parametric family `(.*ba.*){n}` vs `(.*ab.*){n}` (inequivalent) for n = 1..50 — Table 1 of the paper (linear vs quadratic state-space scaling) |

## SMT-LIB conventions

All files are `(set-logic QF_S)` regex equivalence queries. The
typical structure is

```smt2
(assert (not (= R1 R2)))
(check-sat)
```

so the answer is `unsat` when R1 and R2 denote the same regular language
(equivalent) and `sat` when they don't. The `:status` header records the
expected answer — **note** that for some mutation-based benchmarks
(`mutations*/`, `mutations_equiv*/`) the expected status was generated
automatically and is not always correct: some mutations that were
intended to break equivalence accidentally preserve it (e.g. star-to-plus
on a regex whose base contains ε, or intersection with a strictly weaker
constraint).
