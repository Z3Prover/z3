## Scope
PR #11495 head e85a9e8aa6b6b1ed2b579deb15abd6c925e86815, base 8fbb275aba0472e862e289c7af1331b3bd5d512c. Sources fetched via contents API at head: Z3SortedArithmetic.fst sha256 a4982db0..., Z3SortedProof.fst sha256 a56888e1..., Z3SortedSkolem.fst sha256 b36146a9.... Lines: Z3SortedProof.fst 956-979, 1043-1050; Z3SortedArithmetic.fst 287-376.

## Obligations
- O1 (proved, abstract): mapped assumptions (positive premises @ negated conclusion literals) hold iff premises true and no conclusion literal true.
- O2 (proved, abstract, conditional): if the contradiction checker is sound for models satisfying assumptions, the node is sound.
- O3 (proved, abstract): truths distributes over append.
- Real-source obligations (check_contradiction soundness, integer strict-bound adjustment, 4096 budget, Skolem freshness/choice elaboration): INCONCLUSIVE; base modules failed to load: Identifier custard_inline not found in FStar.Attributes (pinned F* 2026.09.27; PR validated with v2026.10.25).

## Correspondence
Model uses a generic eqtype of expressions and a truth function; it abstracts the sorted semantics, Real/integer arithmetic, and the checker. Manual review only for these. Not mechanized C++/OCaml verification.

## Exclusions
Z3SortedSkolem.fst, Z3SortedSkolemTests.fst, Z3Cherry.fst, cherry_runtime/main.cpp, ocaml_runtime, tools/*, prior audit artifacts under fstar/audits/pr-11495/443084f.../, Z3SortedProof Skolem changes. Only the Farkas node mapping was selected (<=3 functions).

## Assumptions
Standard library FStar.List.Tot only; no admits/assumes.

## Reproduce
cd /tmp/gh-aw/agent/fstar-audit; timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --cache_dir cache --odir out --z3rlimit 10 FarkasMappingAudit.fst