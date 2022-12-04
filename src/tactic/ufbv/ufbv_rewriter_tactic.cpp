/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    ufbv_rewriter_tactic.cpp

Abstract:

    UFBV Rewriter (demodulator)

Author:

    Christoph (cwinter) 2012-10-26

Notes:

--*/
#include "tactic/tactical.h"
#include "ast/substitution/demodulator_rewriter.h"
#include "tactic/ufbv/ufbv_rewriter_tactic.h"

class demodulator_rewriter_tactic : public tactic {
    ast_manager & m_manager;
    params_ref    m_params;

public:
    demodulator_rewriter_tactic(ast_manager & m, params_ref const & p):
        m_manager(m), m_params(p) {}

    char const* name() const override { return "ufbv-rewriter"; }

    tactic * translate(ast_manager & m) override {
        return alloc(demodulator_rewriter_tactic, m, m_params);
    }

    void updt_params(params_ref const & p) override {
        m_params.append(p);
    }

    void collect_param_descrs(param_descrs & r) override {
        insert_max_memory(r);
        insert_produce_models(r);
    }

    void operator()(goal_ref const & g, goal_ref_buffer & result) override {
        tactic_report report("ufbv-rewriter", *g);
        fail_if_unsat_core_generation("ufbv-rewriter", g);

        if (g->proofs_enabled()) {
            result.push_back(g.get());
            return;
        }

        demodulator_rewriter dem(m_manager);

        expr_ref_vector forms(m_manager), new_forms(m_manager);

        unsigned size = g->size();
        for (unsigned i = 0; i < size; i++) 
            forms.push_back(g->form(i));

        dem(forms, new_forms);

        g->reset();
        for (expr* fml : new_forms)
            g->assert_expr(fml, nullptr, nullptr);

        // CMW: Remark: The demodulator could potentially
        // remove all references to a variable.

        g->inc_depth();
        result.push_back(g.get());
    }

    void cleanup() override {}

};

tactic * mk_ufbv_rewriter_tactic(ast_manager & m, params_ref const & p) {
    return alloc(demodulator_rewriter_tactic, m, p);
}
