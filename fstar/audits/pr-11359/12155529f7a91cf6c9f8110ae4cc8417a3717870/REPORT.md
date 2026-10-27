Scope: Z3BvLemma.zero_extend_rewrite (+parts guard), Z3BvWord.lemma_append_number, Z3LinearArithmeticEmbed Div case. Only the first two were modelled; the Div change was not modelled.

Obligations (all proved in the abstract model):
1. zero_extend(w,k,x) rewrites to concat(0^k, x): value 0*2^w + x = x. Proved.
2. Width guard w+k<=4096 gives k+w = w+k, so range sort matches the original. Proved.
3. bits_number (xs@ys) = bits_number xs + 2^|xs| * bits_number ys. Proved.

Correspondence: the model reimplements the arithmetic only. The PR modules (Z3BvLemma etc.) were NOT imported or rebuilt, so their actual proofs, the sort side conditions, the concat model law and the zero literal projection are unchecked here. The PR author reports its own full F* build; this audit did not reproduce it.

Assumptions: none beyond F* standard library. Model uses F* 2026.09.27 and Z3 4.13.3 (pinned).

Excluded: Z3LinearArithmeticEmbed Div change (divide a b = Some q guard), Z3NativeProof, Z3SortedProof, Native.fsti operator, cherry_runtime/native.cpp, Z3Native.ml, test tools, benchmarks; C++/OCaml execution, memory safety, and the checker as a whole are not verified. No counterexample was found, but that is not a full proof.

Reproduce: see verification_log.