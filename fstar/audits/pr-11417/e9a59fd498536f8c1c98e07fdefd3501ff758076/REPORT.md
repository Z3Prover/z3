# F* audit: PR #11417 @ e9a59fd498536f8c1c98e07fdefd3501ff758076 (base 668d5979550e899e8341aad1b0a9ad6ff011f821)

Partial scope: 3 changed functions (of the C++ changes), 3 obligations. Tool: F* 2026.09.27, Z3 4.13.3 (pinned release backend).

Source snapshots (head SHA, sha256): src/ast/rewriter/bv_rewriter.cpp `a...` = 921e99c937924dab923b6bf5a7bf2f20a31f19c3a6111740dd66d3ddbdf15b30; src/ast/rewriter/bv2int_translator.cpp = ab3f4c1e7f2c8d21b5c0bc25d3cfdc75e0be3e8acf974bc4740537040b260347.

## Obligations
1. **bv_rewriter::mk_bv_ext_rotate_left/right nested fold (bv_rewriter.cpp ~L2398-2445)** - Intended: folding rot(rot(x,y),z) to rot(x,y+z) (or z-y) preserves rotation amount mod w. 
   - Pre-PR (unguarded) refutation: w=3, bvadd modulus 2^3=8, y=7, z=1: (7+1)%8 %3 = 2 but (7+1)%3 = 0. Checked in F* (`cex_rot_add`, `cex_rot_sub`). This confirms the pre-PR bug; at head the guard `!is_power_of_two(width)` returns BR_FAILED so the witness is excluded. Result for PR head: no counterexample.
2. **Same functions, guarded branch, w = 2^k** - PROVED `fold_add_sound`, `fold_sub_sound`: w | 2^w so wrapping add/sub mod 2^w preserves amount mod w (uses FStar.Math.Lemmas pow2_modulo_modulo_lemma_1; k < 2^k).
3. **bv2int_translator::translate_bv OP_BSMOD (~L471-505)** - PROVED `bsmod_sound`: for N=2^w (even, >=2), x in [0,N), y in (0,N), the translated value, reduced mod N, satisfies the signed bvsmod spec (exists k. r = sx - sy*k, r=0 or sign r = sign y, |r|<|y|), using u = |x| mod |y| with absolute values N-v for v>=N/2 and the sign cases as in the C++ ite chain. The y=0 -> x branch is by definition (outermost if_eq(y,0,x,..)) and not covered by the F* model.

## Mapping / assumptions
F* models integers mathematically; SMT mod/div on positive divisor equals F* % and /. The ite chain is modelled by the `tr` function; rotation amounts are modelled by their effective amounts mod w. Inherited: F* standard library lemmas and Z3 4.13.3 as SMT backend. No admit/assume/axioms.
Final result mod N: the C++ wraps via umod/mod later (abstracted by `% n` in the spec).

## Exclusions (manually reviewed, not proved)
Rotation-by-constant paths, inverse-rotation cancellation (unchanged), test code (src/test/simplifier.cpp, src/test/smt_context.cpp), OP_BSMOD_I identity with OP_BSMOD, is_power_of_two helper itself (util.h), later normalization/wrapping in the translator, memory safety and C++ execution, SAT/UNSAT of the new tests. Model of nested rotation reasons only about amounts; the rotation of the data word by amount mod w is assumed to compose additively.

## Reproduce
fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir c2 --odir o2 Z3PR11417Audit.fst
