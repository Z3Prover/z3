# F* audit PR #11620 @ 326c22ea (partial scope)

Sources (head, contents API): src/model/model_evaluator.cpp sha256 86188fdd44fda8d0aa9d57e43f856137f988f52ee8bd89a2065fc6c103c517ec, evaluator_cfg::reduce_app ITE branch ~L284-292; src/ast/arith_decl_plugin.cpp L961-970 (is_considered_partially_interpreted); rewriter_types.h br_status order (base).

## Obligations (module Pr11620Ite.fst) - all proved
- O1: clamp leaves BR_DONE, BR_FAILED and non-ITE statuses unchanged.
- O2: for ITE, any status < BR_DONE (REWRITE1/2/3/FULL) becomes BR_REWRITE1, i.e. rewrite depth never increases (rewriter_def.h: max_depth=0 -> visit depth 1).
- O3: clamp idempotent.
- O4: refactor to mk_idiv0()/mk_mod0() yields the identical declaration (OP_IDIV0/OP_MOD0, Int x Int -> Int) as the inlined code.

## Correspondence / assumptions
br_status modelled as enum with order from rewriter_types.h (REWRITE1<2<3(FULL<DONE<FAILED). decl modelled as tuple; mk_func_decl hash-consing assumed. Base F* stdlib only; no admits/axioms.

## Not proved / manual review
- Termination or absence of loops in the model evaluator (the PR's actual goal) is NOT proved; only the status-level clamp. Note the clamp reduces BR_REWRITE_FULL/2/3 from bool_rewriter::mk_ite_core (e.g. L103/109/148/165 return BR_REWRITE3, L124/131 REWRITE2) to depth 1, which could in principle leave ITE results less simplified; not analysed.
- Observation (pre-existing, outside PR): arith_util::mk_rem0(expr*,expr*) builds OP_MOD0, not OP_REM0; untouched by PR.
- Excluded: src/test/model_evaluator.cpp tests, rest of evaluator, C++ execution, memory safety.
- Prior audit comment exists for a different SHA (8cdb74ce); this head had none.

Reproduce: see verification.log.
