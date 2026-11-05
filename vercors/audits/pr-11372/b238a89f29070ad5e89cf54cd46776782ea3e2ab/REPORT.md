# VerCors C++ audit, PR #11372 @ b238a89f29070ad5e89cf54cd46776782ea3e2ab (base 02f6a7e1)

Verdict: **inconclusive** (one obligation set verified; non-vacuity witness could not be machine-checked).

## Sources (fetched via contents API at head SHA)
- src/opt/optsmt.cpp sha256 6db97c07...ef (full: 6db97c071b2947aa5108b42f8e9b3ec80dab40755dc096b1bd37b314ccfc9735), lines 742-750 `optsmt::get_base_model` (new); call sites lex L753, box L~960.
- src/opt/optsmt.h sha256 6c9b1bbfb46dd07baa3cf76888e9debf86704bc99cdee98fcf11157a7b414a29
- src/opt/opt_context.cpp sha256 4a5e41fa82d38be1742d5bce83e2b2dd05f8fcf9093b210ee2913d7112cd5ee6: `context::get_base_model` (L449: mdl = m_model), `context::get_labels` (L236: r.append(m_labels)).

## Selected function / obligations (optsmt::get_base_model, the only changed non-test C++ function)
1. O1 (postcondition, model): best_model == context model. **Proved** in extract.
2. O2 (labels frame/copy): after the call, labels length == ctx label count (stale labels discarded by reset). **Proved**.
3. O3 (element equality + memory safety/permissions of the copy loop, loop invariant): labels[i]==ctx_labels[i] for all i, no out-of-bounds. **Proved**, under capacity precondition cap >= ctx_n.

## Correspondence / abstractions (manual)
- model_ref -> int (refcounting, null model not modelled); symbol -> int; svector(symbol) -> array with capacity `cap` and length cell; reset()+append() -> inlined as length:=0 and element-wise copy loop. Capacity growth of svector is replaced by the precondition cap >= ctx_n (svector reallocates; not verified). Callee bodies were inlined from the base-SHA/head-SHA source above, not trusted contracts.
- Separation: ctx labels held at half permission, destination at write; no aliasing between m_labels and context m_labels is assumed (they are distinct members: optsmt::m_labels vs context::m_labels).
- No arithmetic beyond loop index i in [0, ctx_n]; ctx_n>=0 precondition (a size). No overflow issue since i<=ctx_n.

## Non-vacuity
Preconditions are satisfiable (e.g. ctx_n=2, cap=2). A VerCors witness caller unit was attempted but the C++ frontend rejected the call ("It is not possible to call this object"); so non-vacuity is argued manually, not machine-checked. This is why the verdict is not "proved".

## Exclusions
- optsmt::lex / optsmt::box (only call-site substitution of get_base_model; downstream optimization logic unmodelled: STL/virtual calls, exceptions).
- optsmt.h declaration, src/test/opt_bounds.cpp (test), fstar/audits/** (non-C++ audit artefacts).
- Whole-program claim that execute_min_max returns correct labels is out of scope.

## Reproduction
```
mkdir clean && cp OptsmtBaseModel.cpp clean/ && cd clean
/tmp/gh-aw/vercors/vercors --lang cpp --backend silicon --dev-total-timeout 60 $PWD/OptsmtBaseModel.cpp
```
Result: exit 0, `Verification completed successfully.` (also in a fresh directory).
