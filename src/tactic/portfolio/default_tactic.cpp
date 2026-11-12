#include "tactic/portfolio/ff_tactic.h"
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
#include "tactic/ff/ff_solve_tactic.h"
#include "tactic/ff/ff2bv_tactic.h"
#include "tactic/core/simplify_tactic.h"
#include "ast/simplifiers/seq_regular_simplifier.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "params/smt_params_helper.hpp"
#include "tactic/core/elim_uncnstr_tactic.h"
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
namespace {
class automatic_seq_regular_tactic : public dependent_expr_state_tactic {
    params_ref m_params;
public:
    automatic_seq_regular_tactic(ast_manager& m, params_ref const& p):
        dependent_expr_state_tactic(m, p,
            [](ast_manager& m, params_ref const& p, dependent_expr_state& s) -> dependent_expr_simplifier* {
                return alloc(seq_regular_simplifier, m, p, s, true);
            }), m_params(p) {}

    void updt_params(params_ref const& p) override {
        m_params.append(p);
        dependent_expr_state_tactic::updt_params(p);
    }

    tactic* translate(ast_manager& m) override {
        return alloc(automatic_seq_regular_tactic, m, m_params);
    }

    void operator()(goal_ref const& in, goal_ref_buffer& result) override {
        smt_params_helper params(m_params);
        bool has_strings = false;
        bool eligible = params.seq_regular() && params.string_solver() == "nseq" && !in->proofs_enabled();
        for (unsigned i = 0; eligible && i < in->size(); ++i) {
            eligible = !::has_quantifiers(in->form(i));
            if (!has_strings)
                has_strings = seq_regular_simplifier::has_string_terms(in->m(), in->form(i));
        }
        if (eligible && has_strings)
            dependent_expr_state_tactic::operator()(in, result);
        else
            result.push_back(in.get());
    }
};
}

tactic * mk_default_tactic(ast_manager & m, params_ref const & p) {
    tactic* regular = alloc(automatic_seq_regular_tactic, m, p);
    tactic * st = using_params(and_then(regular, mk_simplify_tactic(m, p),
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
                                             // Keep private concatenations intact until unconstrained elimination.
                                             and_then(mk_elim_uncnstr_seq_concat_tactic(m, p), mk_preamble_tactic(m), mk_lazy_tactic(m, p, [&](auto& m, auto const& p) { return mk_smt_tactic(m, p);}))))))))))))))),
                               p);
    // Preserve native equality/Boolean reasoning on residual field goals;
    // the field theory itself supplies exact BV fallback when needed.
    if (m.proofs_enabled())
        return cond(mk_has_ff_probe(), and_then(mk_ff_simplify_tactic(m, p), mk_ff_smt_tactic(m, p)), st);
    return cond(mk_has_ff_probe(), and_then(mk_ff_unique_tactic(m, p), mk_ff_simplify_tactic(m, p), or_else(mk_ff_solve_tactic(m, p), mk_ff_sat_tactic(m, p), mk_ff_smt_tactic(m, p))), st);
}
