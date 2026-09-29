/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    default_tactic.cpp

Abstract:

    General purpose tactic for the Z3 logic (when the logic is not specified).

Author:

    Leonardo (leonardo) 2012-02-22

Notes:

--*/
#include "tactic/portfolio/default_tactic.h"
#include "tactic/tactical.h"
#include "tactic/probe.h"
#include "ast/for_each_expr.h"
#include "ast/ff_decl_plugin.h"
#include "tactic/arith/ff_solve_tactic.h"
#include "tactic/arith/ff2bv_tactic.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/smtlogics/qfbv_tactic.h"
#include "tactic/smtlogics/qflia_tactic.h"
#include "tactic/smtlogics/qflra_tactic.h"
#include "tactic/smtlogics/qfnia_tactic.h"
#include "tactic/smtlogics/qfnra_tactic.h"
#include "tactic/smtlogics/nra_tactic.h"
#include "tactic/arith/probe_arith.h"
#include "tactic/smtlogics/quant_tactics.h"
#include "tactic/fpa/qffp_tactic.h"
#include "tactic/fpa/qffplra_tactic.h"
#include "tactic/smtlogics/qfaufbv_tactic.h"
#include "tactic/smtlogics/qfauflia_tactic.h"
#include "tactic/fd_solver/fd_solver.h"
#include "tactic/smtlogics/smt_tactic.h"


// SMT fallback for field goals. Over large fields, relevancy propagation
// costs 20-40 % on the goals that reach this stage and gives nothing back.
// Over small fields the goal is mostly bit-blasted and search behaves better
// with relevancy, so the default is kept there.
namespace {
    class ff_small_field_probe : public probe {
    public:
        result operator()(goal const &g) override {
            ast_manager &m = g.m();
            ff_util ff(m);
            bool small = false;
            auto visit = [&](expr *e) {
                if (ff.is_ff(e) && ff.modulus(e->get_sort()) < rational(1 << 16))
                    small = true;
            };
            for (unsigned i = 0; i < g.size() && !small; ++i)
                for_each_expr(visit, g.form(i));
            return result(small);
        }
    };
}

static tactic *mk_ff_smt_tactic(ast_manager &m, params_ref const &p) {
    params_ref q;
    q.set_uint("relevancy", 0);
    return cond(alloc(ff_small_field_probe), mk_smt_tactic(m, p), using_params(mk_smt_tactic(m, p), q));
}

tactic * mk_default_tactic(ast_manager & m, params_ref const & p) {
    tactic * st = using_params(and_then(mk_simplify_tactic(m, p),
                                        cond(mk_and(mk_is_propositional_probe(), mk_not(mk_produce_proofs_probe())),
                                             mk_lazy_tactic(m, p, [&](auto& m, auto const& p) { return mk_fd_tactic(m, p); }),
                                        cond(mk_is_qfbv_probe(), mk_lazy_tactic(m, p, [&](auto& m, auto const& p) { return mk_qfbv_tactic(m, p); }),
                                        cond(mk_is_qfaufbv_probe(), mk_lazy_tactic(m, p, [&](auto& m, auto const& p) { return mk_qfaufbv_tactic(m, p); }),
                                        cond(mk_is_qflia_probe(), mk_lazy_tactic(m, p, [&](auto& m, auto const& p) { return mk_qflia_tactic(m, p); }),
                                        cond(mk_is_qfauflia_probe(), mk_lazy_tactic(m, p, [&](auto& m, auto const& p) { return mk_qfauflia_tactic(m, p); }),
                                        cond(mk_is_qflra_probe(), mk_lazy_tactic(m, p, [&](auto& m, auto const& p) { return mk_qflra_tactic(m, p); }),
                                        cond(mk_is_qfnra_probe(), mk_lazy_tactic(m, p, [&](auto& m, auto const& p) { return mk_qfnra_tactic(m, p); }),
                                        cond(mk_is_qfnia_probe(), mk_lazy_tactic(m, p, [&](auto& m, auto const& p) { return mk_qfnia_tactic(m, p); }),
                                        cond(mk_is_lira_probe(), mk_lazy_tactic(m, p, [&](auto& m, auto const& p) { return mk_lira_tactic(m, p); }),
                                        cond(mk_is_nra_probe(), mk_lazy_tactic(m, p, [&](auto& m, auto const& p) { return mk_nra_tactic(m, p); }),
                                        cond(mk_is_qffp_probe(), mk_lazy_tactic(m, p, [&](auto& m, auto const& p) { return mk_qffp_tactic(m, p); }),
                                        cond(mk_is_qffplra_probe(), mk_lazy_tactic(m, p, [&](auto& m, auto const& p) { return mk_qffplra_tactic(m, p); }),
                                        //cond(mk_is_qfufnra_probe(), mk_qfufnra_tactic(m, p),
                                             and_then(mk_preamble_tactic(m), mk_lazy_tactic(m, p, [&](auto& m, auto const& p) { return mk_smt_tactic(m, p);}))))))))))))))),
                               p);
    // Preserve native equality/Boolean reasoning on residual field goals;
    // the field theory itself supplies exact BV fallback when needed.
    return cond(mk_has_ff_probe(), and_then(mk_ff_unique_tactic(m, p), mk_ff_simplify_tactic(m, p), or_else(mk_ff_solve_tactic(m, p), mk_ff_sat_tactic(m, p), mk_ff_smt_tactic(m, p))), st);
}
