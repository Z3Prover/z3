/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    macro_finder_tactic.cpp

Abstract:

    Macro finder

Author:

    Christoph (cwinter) 2012-10-26

Notes:

--*/
#include "tactic/tactical.h"
#include "ast/macros/macro_manager.h"
#include "ast/macros/macro_finder.h"
#include "tactic/generic_model_converter.h"
#include "tactic/ufbv/macro_finder_tactic.h"

class macro_finder_tactic : public tactic {

    struct imp {
        ast_manager & m_manager;
        bool m_elim_and;

        imp(ast_manager & m, params_ref const & p) :
            m_manager(m),
            m_elim_and(false) {
            updt_params(p);
        }

        ast_manager & m() const { return m_manager; }


        void operator()(goal_ref const & g,
                        goal_ref_buffer & result) {
            tactic_report report("macro-finder", *g);
            TRACE("macro-finder", g->display(tout););

            bool produce_proofs = g->proofs_enabled();
            bool unsat_core_enabled = g->unsat_core_enabled();
            macro_manager mm(m_manager);
            macro_finder mf(m_manager, mm);

            expr_ref_vector forms(m_manager), new_forms(m_manager);
            proof_ref_vector proofs(m_manager), new_proofs(m_manager);
            expr_dependency_ref_vector deps(m_manager), new_deps(m_manager);
            unsigned size = g->size();
            for (unsigned idx = 0; idx < size; idx++) {
                forms.push_back(g->form(idx));
                proofs.push_back(g->pr(idx));
                deps.push_back(g->dep(idx));
            }

            mf(forms, proofs, deps, new_forms, new_proofs, new_deps);

            g->reset();
            for (unsigned i = 0; i < new_forms.size(); i++)
                g->assert_expr(new_forms.get(i),
                               produce_proofs ? new_proofs.get(i) : nullptr,
                               unsat_core_enabled ? new_deps.get(i) : nullptr);

            generic_model_converter * evmc = alloc(generic_model_converter, mm.get_manager(), "macro_finder");
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
            m_elim_and = p.get_bool("elim_and", false);
        }
    };

    imp *      m_imp;
    params_ref m_params;
public:
    macro_finder_tactic(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(macro_finder_tactic, m, m_params);
    }

    ~macro_finder_tactic() override {
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
        r.insert("elim_and", CPK_BOOL, "(default: false) eliminate conjunctions during (internal) calls to the simplifier.");
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

tactic * mk_macro_finder_tactic(ast_manager & m, params_ref const & p) {
    return alloc(macro_finder_tactic, m, p);
}
