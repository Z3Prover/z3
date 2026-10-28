# F* audit of PR #11415 at 07e7ff68e9512ea206185a09c9c9a7e5b1d8cf9f (base c698bae880c654763b09d29b634b38562eafea11)

Scope: PARTIAL. Source: src/smt/smt_quantifier.cpp patch (patch hash/line ranges taken from the GitHub files API; full functions not fetched at head, only the patch hunks at +653..+1100 were read).

## Selected changed functions (3) and obligations (<=3 each)
1. arith_unify (equation solving step): O1 - binding variable x := (-1/c)*rest when c*x+rest=0 satisfies the equation (exact rational arithmetic model, c != 0 guaranteed by arith_coefficient returning false on zero).
2. arith_match (instance construction): O2 - reversed term layout: terms pushed for i=n-1 downto inner_decls give list index j <-> variable n-1-j (de Bruijn order expected by add_instance), and guarded_terms.set(nt-i-1,..) / substitution entry source_terms[size-k-1] address exactly variable i / lo+k. 
3. add_arith_instance / arith_match emission: O3 - an instance of the original forall quantifier with exactly nq terms (arity check) is entailed by the quantifier; length of the emitted binding list equals nq.
Results: O1 proved, O2 (both slot lemmas) proved, O3 proved (all checked by F*, exit 0).

## Counterexample search
No concrete reachable witness was constructed; none claimed. Failed attempts are not evidence either way.

## Correspondence and assumptions
- rat models mpq (num/den, den>0); the models are value-level, not C++ execution. Rewriter normalization (th_rewriter) is assumed to preserve arithmetic equality.
- O2 models index arithmetic only; C++ conditions that the binding vector has exactly nq entries rely on source.inner_decls <= ns, which was manually read (inner_decls bounded since inner+nested+q decls <= 4) but not mechanized.
- O3 assumes quantifier semantics: forall body true for all tuples of reals; instances use only terms of the right sort (real), manual review.
- Standard F* library only; no base fstar/ modules imported. No admit/assume/axioms.

## Manually reviewed, NOT mechanized / excluded
- Excluded changed code: get_arith_bounds, arith_eliminate, arith_coefficient, arith_atom, arith_match() driver, budget logic, final_check_quant/init_search_eh hooks, qi_params, smt_params_helper, quant_tactics.cpp (UFLRA macro / QSAT routing), CMakeLists, src/test/smt_context.cpp.
- Not verified: termination/budget bounds, memory safety, enode generation handling, proof production (instances go via m_qm->add_instance, existing proof-producing path), soundness of the QSAT routing change, expr_safe_replace behaviour, offsets +/-1 (these are only candidate bindings; instances of a forall are always sound, so offsets do not affect soundness).
- Observation (not a counterexample): in arith_match, `ground.insert(variable, anchor)` with anchor possibly 0 if no constant found: only affects completeness, instances remain sound.

## Reproduce
cd /tmp/gh-aw/agent/fstar-audit; bash run.sh  (fstar.exe 2026.09.27, z3 4.13.3 pinned; --z3rlimit 10, 120s timeout, fresh cache)
