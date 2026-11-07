# F* audit PR 11551 @ d5c22e60594278354d1b1d345a3eae8af3a95082 (base 684853cb)

Source: src/ast/ast_smt2_pp.cpp at head, sha256 c092f93b8dca4715035ea2b93197b68d2984ebb5a955b59a8a38401331a9651f, lines ~793-803 (new concat branch in process_app).

## Obligations (all proved)
1. cat_wf: concatenation of well-formed bit-vectors (v<2^w) is well-formed.
2. cat_assoc: binary concat is associative, so the printed left-nested ((x0 x1) x2)... denotes the same value/width as n-ary concat (right-nested reference).
3. fold_correct: the C++ left fold foldl_cat acc l equals nary semantics; nary_wf preserves well-formedness. Arity: branch guard num_args>2 guarantees the two initial *it++ reads are valid (patch_arity_ok).

## Correspondence / assumptions
bv models value+width as naturals; cat a b = a*2^wb+b. Models the formatted-string structure only semantically (nesting order), not formatting strings, memory, or format object lifetimes (format_ref handling of intermediate results is manually reviewed only). The SMT-LIB standard concat is binary, assumed as the target. Z3 concat n-ary is assumed to put args in high-to-low order, same as the binary nesting. Base/standard libs: FStar.Math.Lemmas, FStar.List.Tot.

## Exclusions
- pp_fdecl_name rename of OP_BSDIV_I/BUDIV_I/BSREM_I/BUREM_I/BSMOD_I to bvsdiv/bvudiv/bvsrem/bvurem/bvsmod (not modelled; note that this prints the total _i variants as the standard names, which differ at divisor zero from SMT-LIB defined semantics only in how solver interprets; not proved).
- src/test/smt2print_parse.cpp tests.
- Not mechanized verification of C++ execution.

Prior audit markers exist for earlier heads ea08a548 and bddf23d5; this is for the new head.

## Reproduce
fstar.exe --smt z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache1 --odir out1 Pr11551ConcatFold.fst