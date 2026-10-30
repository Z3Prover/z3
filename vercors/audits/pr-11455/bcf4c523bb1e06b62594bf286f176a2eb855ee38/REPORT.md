# VerCors C++ audit, PR 11455 @ bcf4c523bb1e06b62594bf286f176a2eb855ee38 (base dad37c85122de03ec838d3d8528de1f341ead036)

Verdict: **inconclusive** (partial scope; only a weak guard obligation proved).

Source: src/ast/rewriter/finite_set_axioms.cpp at head, sha256 ab5b057de7d02e0d926063da06b4a1be6ea86e441eb528d28c109b85b686215d, function finite_set_axioms::size_ub_axiom, new lines 345-353. Callee sort_size from ast.h (trusted base, lines 310-347).

## Obligations (one function)
1. O1 emitted-iff-finite: the bound `|A| <= N` is emitted exactly when `domain_size.is_finite()` (and the bound equals the size field). **Proved** (SizeBound.cpp, `emitted`, `bound_value`).
2. O2 width correspondence: sort_size::m_size is uint64_t and `rational(domain_size.size())` is exact. **Inconclusive**: VerCors C++ frontend rejects `unsigned long` ("TypeSpecifier1Context ... not supported", attempts 1-2 retained below), so unsigned 64-bit semantics could not be faithfully modelled; the extract uses mathematical-int-like `int`, which does NOT model uint64. Source reading suggests sort_size(rational) maps values > uint64 to VERY_BIG, which is skipped by the guard.
3. O3 semantic soundness (|A| <= |element domain| for every sort whose get_num_elements is finite): **Inconclusive**, not expressible without modelling Z3 sorts/expressions/semantics; no counterexample found. Not claimed (see the F* audit for this).

## Correspondence / abstractions
sort_size reduced to (kind:int, size:int); kind 0=FINITE,1=VERY_BIG,2=INFINITE. Expression building, m_rewriter and add_unit are omitted. The `VERIFY(u.is_finite_set(...))` precondition and elem_sort non-null are not verified. Preconditions: `kind==0 ==> size>=0` (justified: unsigned field); non-vacuous (kind=0,size=2 satisfies). The `kind` values and their mapping are manual.

## Exclusions
src/test/finite_set.cpp (test code), fstar/audits/** (other audits), the rest of size_ub_axiom (unchanged).

## Failed/omitted attempts
1. class with `unsigned long` field: parse failure, unsupported. 2. same with `long`: parse failure (class with member method/bool pattern unsupported). 3. pointer out-params with `&emitted[0]`: "not a heap location". Those units omitted.

## Reproduce
mkdir d && cp SizeBound.cpp d/ && cd d && /tmp/gh-aw/vercors/vercors --lang cpp --backend silicon --dev-total-timeout 60 $PWD/SizeBound.cpp  (VerCors 2.4.0, OpenJDK 17.0.21, bundled Z3; exit 0, "Verification completed successfully.")
