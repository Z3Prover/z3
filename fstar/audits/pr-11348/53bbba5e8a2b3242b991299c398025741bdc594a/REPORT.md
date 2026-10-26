## Obligations (all proved)
1. basic_cmds.cpp:523-530 set_option global-decls: re-setting the current value never throws and leaves state unchanged (o1); a differing value behaves as before (o2); an initialized context's global_decls is never altered (o3).
2. qsat.cpp:1275-1290: proofs enabled => fails before any work (q1); otherwise identical to old (q2).
3. theory_lra.cpp ~328, ~1302 and theory_arith_core.h ~63: with proofs, mk_th_axiom replaces untracked assign (a2); without proofs unchanged (a1).

## Correspondence
F* models only the branch guards (init flag, global_decls value, proofs_enabled); C++ side effects are abstracted to constructor tags.

## Assumptions
Not proved: mk_th_axiom yields a sound axiom with a proof term; fail_if_proof_generation throws when proofs are on; check_not_initialized throws iff initialized. No base modules imported.

## Exclusions
src/api/ml/CMakeLists.txt (linker flags), all fstar/*.fst/.ml/.py/.ps1/.json changes, fstar/audits files, and any behavior beyond these three functions (six call sites in theory_lra/theory_arith counted as one). Source taken from PR patch excerpts, not full function bodies; memory safety and AST plumbing manually unreviewed. Not mechanized C++ verification.

## Reproduce
In a fresh dir: fstar.exe --smt z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out Z3Pr11348Guards.fst (F* 2026.09.27, Z3 4.13.3).
