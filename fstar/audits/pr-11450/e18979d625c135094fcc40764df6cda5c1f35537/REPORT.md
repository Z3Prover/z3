fstar-nfv-audit:e18979d625c135094fcc40764df6cda5c1f35537

Scope (partial): PR #11450 head e18979d625c135094fcc40764df6cda5c1f35537 (base f87e9c80df2fb6820bb724fcbea2ee664b54fab2). Only the new typed predicates in fstar/Z3CanonicalOps.fst (sha256 of head file 77695fe814a861f2283757b03f03c10e7c0379af64f376f49c3e0ed5df664434) were audited, fetched via contents API at the head SHA.

Obligations (all proved):
1. A decl named "=" tagged BV ult (114) is not canonical_eq / canonical_connective (the master false-accept clash).
2. A decl named "and" tagged datatype accessor (202), any domain/range, is not a canonical connective.
3. Every canonical connective has tag != 114 and != 202 (tag-disjointness; also the PR's own lemma_canonical_tag).
The unmodified head Z3CanonicalOps.fst verifies as a dependency, including its own lemmas.

Correspondence: F* func_decl / canonical_* model name+tag+domain+range+params checks of the C++/OCaml bridge declarations. Not mechanized: C++ execution, native marshaling fidelity, the parser, memory safety.

Assumptions: base modules Z3AstTheory/Z3ValueTheory and F* stdlib; tag numbers 114/202 taken from Z3BvLemma/Z3DatatypeLemma on the base.

Excluded: Z3BvExhaustive.fst, Z3StandardModel.fst (ground_model inhabitedness, lemma_standard_model, lemma_valid_ground), Z3BvExhaustiveTests.fst, tooling/doc changes. The PR itself states global model_sound remains vacuous; nothing here changes that. No counterexample found.

Reproduce: F=/tmp/gh-aw/fstar/bin/fstar.exe; $F --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include (base)/fstar --include . --z3rlimit 10 --cache_dir cache --odir out AuditCanonicalOps.fst
