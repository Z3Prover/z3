## Scope
Head 9225942635d705ff5eec6eb76405dd63a8bb50e3, base 9c7b1c6513ea0beb492f406dc7c29a85b175835e. Changed function: Z3IntegerDivision.check (fstar/Z3IntegerDivision.fst, hunk @@ -98,7 +99,7): guard `f.decl_name = "or" && f.interp = Some op_or` replaced by `C.canonical_or f` (name, tag, all-Boolean domain, Boolean range, no int_params); the existing domain=[bool;bool] and range checks remain.

## Obligations (all proved)
- O1: new guard implies old guard (no newly accepted declarations).
- O2: newly rejected declarations are exactly ones carrying int_params.
- O3: concrete witness shows the tightening is real and a clashing tag is rejected.

## Correspondence/assumptions
Model re-declares func_decl fields with abstract int sorts and op_or=5 (copied from the shape of Z3CanonicalOps.canonical_or, fetched at head); it does not import PR modules. This is a semantic guard-shape audit, not mechanized C++ verification. Whether native bridge decls ever carry int_params for or is manually unreviewed; if so, valid proofs would be rejected (completeness, not soundness).

## Exclusions
Z3QuantifierKernel.fst (fetched, not audited), Z3CoreKernel, Z3CoreModel, Z3StandardModel, Z3GhostStandardModel, Z3BvExhaustive, Z3BvWord, Z3ArithmeticFactor candidate_shape, Z3ResolutionProofTheory, all tests, docs and OCaml/Python tools. Earlier-audited items (CanonicalOps, arith axiom, BvWord arithmetic) not repeated.

## Reproduce
fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir c --odir o AuditOrGuard.fst