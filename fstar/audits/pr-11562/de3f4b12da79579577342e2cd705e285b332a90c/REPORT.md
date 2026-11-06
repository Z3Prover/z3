# F* audit of PR 11562 @ de3f4b12da79579577342e2cd705e285b332a90c (base 5bab8997)

Changed since previously audited 2304e7c2: smt_context.cpp (cache_generation: insert only for forall), smt_internalizer.cpp (internalize_quantifier: m_qmanager->add / quantifier flag / cached generation only for forall; exists runs positive pass when polarity != l_false; undo_mk_bool_var: del only for forall), src/test/smt_context.cpp (excluded). Source hashes (sha256): smt_context.cpp 21c4658e496c90569a8cf4893b2b3cb0b016b3555c7f48576c8a70fab81dbd94; smt_internalizer.cpp 8f4dd845f02525dca2ccfa05c152a2e00dbcff57733b07db3edbe0f38b4a7291. Lines: smt_internalizer.cpp 655-676, 1111-1120; smt_context.cpp 2378-2385.

## Obligations (all proved)
- O1: registration, deletion and generation caching are all forall-only, so add/del are symmetric and exists is never registered/deleted/cached.
- O2: exists gets the positive pass iff polarity != l_false, negative pass iff polarity != l_true; forall never gets the positive pass.
- O3: seen-set marking per polarity is idempotent and independent across polarities.

## Assumptions / exclusions
Abstract model: lbool encoded as ints; NNF correctness, proof terms, trail rollback, qmanager internals (e.g. that del on unregistered quantifiers would have been harmful), m_cached_generation consumers, and the test file are not modeled. Not mechanized verification of C++. No counterexample sought beyond the model; none found. Base modules not imported; no admits/assumes.

## Reproduce
fstar.exe 2026.09.27 with Z3 4.13.3: see verification log.