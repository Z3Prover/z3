# F* audit PR #11693 @ 62841fdb

Source: src/qe/qsat.cpp at head, fetched via contents API (sha256 c74f8d40efcac6c9fa8cdec66f22c13b672ad434627907b0ebfd8f1f97c864ef), lines ~1333-1340 (loop setting fml = mk_false when any m_answer conjunct is_false).

## Property
Short-circuiting the answer to false must not change its meaning, and must give a false formula whatever the later rebinding.

## Obligations (all proved)
1. o1: pr_fml l = conj l (replacement preserves the conjunction semantics).
2. o2_exists/o2_forall: exists/forall over a nonempty domain of a constant-false body is false (so rebinding is not needed once fml is false; in C++ the rebinding loop skips vars that do not occur in false, so no quantifier is added).
3. o3: the old output forall(...)(and ... false) was semantically false too, so the PR changes representation (syntactic false, recognised by the goal), not meaning.

## Mapping
m_answer -> list bool of conjunct truth values; mk_and -> conj; m.is_false(a) -> mem false. Quantifier rebinding -> predicates over a nonempty domain.

## Assumptions
Standard F* library (FStar.List.Tot) only; nonempty domains; m_answer conjuncts are sound qe results. Not proved: that m_answer is correct, C++ execution, memory safety, AST plumbing, that the goal recognises false and that qe2 now answers unsat (covered only by the PR test, not run).

## Exclusions
src/test/smt_context.cpp (test only). No other changed functions.

## Reproduce
/tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include /home/runner/work/z3/z3/fstar --cache_dir cache --odir out --z3rlimit 10 QsatFalseAnswer.fst


## Versions
F* 2026.09.27
platform=Linux_x86_64
system=Unix
compiler=OCaml 5.3.0
date=2026-09-27 16:52:08 +0000
commit=7deb38a27c86990664c6b41e4b6093597acdebd4
Z3 version 4.13.3 - 64 bit
