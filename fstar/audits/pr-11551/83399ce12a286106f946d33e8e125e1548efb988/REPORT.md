# F* audit PR 11551 @ 83399ce12a286106f946d33e8e125e1548efb988

fstar-nfv-audit:83399ce12a286106f946d33e8e125e1548efb988

Base: 814fda3f33f613f2e44a120808a60c2f1876f7c9. Source: src/ast/ast_smt2_pp.cpp at head (sha256 558f9d809c92cadb2ae949da9e52f72406563f38fbe92b127e68515dcd0556fa), lines 748-830 (new branch 778-788).

## Change
For bit-vector concat with more than 2 args, the printer now emits left-nested binary `(concat (concat a b) c)` instead of n-ary `(concat a b c)`, which is not SMT-LIB compliant.

## Obligations (all proved)
1. Value preservation: eval(printed) = append of all arg values (fold_sem / print_sem).
2. Argument order preserved (same lemma; append is order-sensitive).
3. Width preservation: width(printed) = sum of arg widths (width_ok).
Plus an assert_norm witness for the 3-arg test shape of the PR.

## Mapping
bit-vector = bool list, concat = append, the branch loop = fold_cat starting from Cat a b. Guard: is_app_of(t,bv_family_id,OP_CONCAT) && num_args>2; 2-arg concat falls through to the generic path (already binary).

## Manually reviewed (not mechanized)
- `*it++` inside a braced initializer list is sequenced left to right, so the first two args are a then b.
- flat_assoc may splice nested unshared concat children into the parent's arg stack; the branch consumes whatever args are on the stack, so output stays binary and semantically equal by associativity of concat.
- mk_compose/format_ref refcounting, memory safety and C++ execution are not verified; the new test in src/test/smt2print_parse.cpp was not run.

## Exclusions
src/test/smt2print_parse.cpp, .github/scripts, fstar/** proof and runtime edits, previous audit directories.

## Assumptions
F* standard library FStar.List.Tot (append_assoc, append_l_nil, append_length); no base modules imported; no admit/assume.

## Reproduce
/tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out Pr11551Head8339.fst
F* 2026.09.27, Z3 4.13.3 (pinned release).