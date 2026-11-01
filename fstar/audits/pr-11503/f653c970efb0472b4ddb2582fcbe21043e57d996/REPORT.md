Base 8fbb275a, head f653c970. main.cpp sha256 41b49379..., readable.h sha256 6de1e680.... 

Obligations (entry_at, lambda in readable_report): O1 negative index -> None; O2 in-range index i returns i-th entry; O3 out-of-range -> None (no walk past list end). All proved.

Correspondence: cons list modelled as F* list; C++ walks cells with a position counter and nullptr on non-scalar/negative index. Assumes cherry_is_scalar/cherry_int_to_u64 convert correctly and list terminates (well-formed immutable list). Manual review: readable report is diagnostic stderr output only; verdicts (REJECT/ACCEPT) are computed before it and not altered in the diff. Not mechanized: C++ execution, memory safety overall, string formatting, family grouping/sorting, readable.h (410 lines), OCaml Z3NativeMain.ml changes, and test files. Excluded: all those. Semantic proofs do not verify C++ execution.

Reproduce: /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include /home/runner/work/z3/z3/fstar --z3rlimit 10 --cache_dir cache --odir out ReadableEntryAt.fst
F* 2026.09.27, Z3 4.13.3. No counterexample sought beyond review; none found.