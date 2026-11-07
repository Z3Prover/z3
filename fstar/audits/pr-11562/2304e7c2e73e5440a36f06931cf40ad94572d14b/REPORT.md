# F* audit PR #11562 @ 2304e7c2e73e5440a36f06931cf40ad94572d14b (base 5bab89972dc48c2d5560b1e6e0df8297bd85e2ea)

PR open at this SHA; no prior marker for it. Source sha256 at head: smt_internalizer.cpp 1450b7045ebda8da56cd2f88edcdec1691d7c4f45a8c7fdbe5cebdeac0a2364f; smt_context.h 0850a3a3b72c373d91861693b2332d6ccee16a35b8af28b8d3400f6f961b1d4e.

## Obligations (all PROVED in the abstract model)
Changed functions: context::internalize_formula (polarity threading), internalize_quantifier, internalize_quantifier_polarity.
1. O1: lbool operator~ (util/lbool.h integer negation) is an involution, swaps true/false, fixes undef; to_lbool(!sign) is valid.
2. O2: Not-gate flip is exact on possible occurrence polarities; every possibly-negative occurrence (p != l_true) gets the negative NNF/Skolem clause; l_undef gets both.
3. O3: seen-set revisits under other polarities are monotone and idempotent; coverage for earlier and later polarities is preserved.
4. O4: clause ~premise \/ result with premise=literal(q,!positive) equals source -> result.
5. O5: default l_undef calls (gate args, ite condition) get both polarities.

## Correspondence and assumptions
Polarity is an int with the C++ encoding (false=-1, undef=0, true=1). NNF result correctness is assumed from existing base audits (fstar/Z3QuantifierNnf.fst), not re-proved. Trail/scope undo of m_quantifier_positive/negative, proof terms, enode creation for quantifiers, on_scope_exit cleanup, and relevancy watches are NOT mechanized and remain manually reviewed. Semantic model only; not verification of C++ execution, memory safety, or the solver.

## Exclusions
src/test/smt_context.cpp; call-site argument edits (arith_eq_adapter, seq_regex, smt_context.cpp, smt_model_finder, theory_array_base, theory_ff, theory_lra); earlier audit artifacts in the PR; end-to-end claim that issue #11556 is fixed.

## Reproduce
See verification log (F* 2026.09.27, Z3 4.13.3, z3rlimit 10, fresh cache).