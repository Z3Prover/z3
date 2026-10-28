# F* audit PR #11415 head 3082d1f9477924706c44fc1adde02cf6ec24f7a8 (base c698bae8)
PARTIAL scope: delta since audited head 229256ea in src/smt/smt_quantifier.cpp (lines ~706-787 new `arith_scaled_polynomial`; call-site change ~929-941 in bound extraction). One function, three abstract obligations.
Obligations (rational model, den>0):
- S1 proved: denominator 1+|scale| (ite(scale>=0,scale,-scale)) is strictly positive, so mk_div never divides by zero.
- S2 proved: for a monomial sharing all scale factors, emitted `remaining` = monomial/scale when scale<>0 (code comment says hints, not identities).
- S3 proved: non-shared monomial m -> m/(1+|s|) preserves sign/zero-ness; and a concrete check (m=s=1) that it is NOT a division identity, i.e. it is a heuristic hint, as the code comment states. This is not a soundness counterexample: the result feeds instance hints, not asserted equalities.
Assumptions: abstract rationals; flatten bounds (<=8 inspected, <=4 factors) and pointer-equality factor matching modeled as given; scale factors treated as real-valued.
Excluded: all other changed code (smt_context test, bound extraction rest, elimination, tactics), AST plumbing, memory safety, C++ execution. Mixed shared/non-shared monomials: the resulting polynomial's role as a sound bound relies on later checks, not modeled.
Reproduce: see verification.log.
