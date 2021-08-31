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
#include "tactic/ufbv/ufbv_rewriter.h"
#include "tactic/ufbv/ufbv_rewriter_tactic.h"

class ufbv_rewriter_tactic : public tactic {
    ast_manager & m_manager;
    params_ref    m_params;

public:
    ufbv_rewriter_tactic(ast_manager & m, params_ref const & p):
        m_manager(m), m_params(p) {}

    tactic * translate(ast_manager & m) override {
        return alloc(ufbv_rewriter_tactic, m, m_params);
    }

    void updt_params(params_ref const & p) override {
        m_params = p;
    }

    void collect_param_descrs(param_descrs & r) override {
        insert_max_memory(r);
        insert_produce_models(r);
        insert_produce_proofs(r);
    }

    void operator()(goal_ref const & g, goal_ref_buffer & result) override {
        tactic_report report("ufbv-rewriter", *g);
        fail_if_unsat_core_generation("ufbv-rewriter", g);

        bool produce_proofs = g->proofs_enabled();

        ufbv_rewriter dem(m_manager);

        expr_ref_vector forms(m_manager), new_forms(m_manager);
        proof_ref_vector proofs(m_manager), new_proofs(m_manager);

        unsigned size = g->size();
        for (unsigned i = 0; i < size; i++) {
            forms.push_back(g->form(i));
            proofs.push_back(g->pr(i));
        }

        dem(forms.size(), forms.data(), proofs.data(), new_forms, new_proofs);

        g->reset();
        for (unsigned i = 0; i < new_forms.size(); i++)
            g->assert_expr(new_forms.get(i), produce_proofs ? new_proofs.get(i) : nullptr, nullptr);

        // CMW: Remark: The demodulator could potentially
        // remove all references to a variable.

        g->inc_depth();
        result.push_back(g.get());
    }

    void cleanup() override {}

};

tactic * mk_ufbv_rewriter_tactic(ast_manager & m, params_ref const & p) {
    return alloc(ufbv_rewriter_tactic, m, p);
}
