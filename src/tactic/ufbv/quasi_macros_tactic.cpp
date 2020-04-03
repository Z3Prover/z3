/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    quasi_macros_tactic.cpp

Abstract:

    Quasi-Macros

Author:

    Christoph (cwinter) 2012-10-26

Notes:

--*/
#include "tactic/tactical.h"
#include "tactic/generic_model_converter.h"
#include "ast/macros/macro_manager.h"
#include "ast/macros/macro_finder.h"
#include "ast/macros/quasi_macros.h"
#include "tactic/ufbv/quasi_macros_tactic.h"

class quasi_macros_tactic : public tactic {

    struct imp {
        ast_manager & m_manager;

        imp(ast_manager & m, params_ref const & p) : m_manager(m) {
            updt_params(p);
        }

        ast_manager & m() const { return m_manager; }


        void operator()(goal_ref const & g,
                        goal_ref_buffer & result) {
            tactic_report report("quasi-macros", *g);

            bool produce_proofs = g->proofs_enabled();
            bool produce_unsat_cores = g->unsat_core_enabled();
                            
            macro_manager mm(m_manager);
            quasi_macros qm(m_manager, mm);

            expr_ref_vector forms(m_manager);
            proof_ref_vector proofs(m_manager);
            expr_dependency_ref_vector deps(m_manager);

            unsigned size = g->size();
            for (unsigned i = 0; i < size; i++) {
                forms.push_back(g->form(i));
                proofs.push_back(g->pr(i));
                deps.push_back(g->dep(i));
            }

            do { 
                tactic::checkpoint(m());
            } 
            while (qm(forms, proofs, deps));

            g->reset();
            for (unsigned i = 0; i < forms.size(); i++)
                g->assert_expr(forms.get(i),
                               produce_proofs ? proofs.get(i) : nullptr,
                               produce_unsat_cores ? deps.get(i, nullptr) : nullptr);

            generic_model_converter * evmc = alloc(generic_model_converter, mm.get_manager(), "quasi_macros");
            unsigned num = mm.get_num_macros();
            for (unsigned i = 0; i < num; i++) {
                expr_ref f_interp(mm.get_manager());
                func_decl * f = mm.get_macro_interpretation(i, f_interp);
                evmc->add(f, f_interp);
            }
            g->add(evmc);
            g->inc_depth();
            result.push_back(g.get());
        }

        void updt_params(params_ref const & p) {
        }
    };

    imp *      m_imp;
    params_ref m_params;

public:
    quasi_macros_tactic(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(quasi_macros_tactic, m, m_params);
    }

    ~quasi_macros_tactic() override {
        dealloc(m_imp);
    }

    void updt_params(params_ref const & p) override {
        m_params = p;
        m_imp->updt_params(p);
    }

    void collect_param_descrs(param_descrs & r) override {
        insert_max_memory(r);
        insert_produce_models(r);
        insert_produce_proofs(r);
    }

    void operator()(goal_ref const & in,
                    goal_ref_buffer & result) override {
        (*m_imp)(in, result);
    }

    void cleanup() override {
        ast_manager & m = m_imp->m();
        imp * d = alloc(imp, m, m_params);
        std::swap(d, m_imp);
        dealloc(d);
    }

};

tactic * mk_quasi_macros_tactic(ast_manager & m, params_ref const & p) {
    return alloc(quasi_macros_tactic, m, p);
}
