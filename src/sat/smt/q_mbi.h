/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    q_mbi.h

Abstract:

    Model-based quantifier instantiation plugin

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-29

--*/
#pragma once

#include "solver/solver.h"
#include "qe/mbp/mbp_plugin.h"
#include "sat/smt/sat_th.h"
#include "sat/smt/q_model_fixer.h"

namespace euf {
    class solver;
}

namespace q {

    class solver;

    class mbqi {
        struct stats {
            unsigned m_num_instantiations;
            
            stats() { reset(); }

            void reset() {
                memset(this, 0, sizeof(*this));
            }
        };
        struct q_body {
            app_ref_vector  vars;
            expr_ref        mbody;   // body specialized with respect to model
            expr_ref_vector vbody;   // (negation of) body specialized with respect to vars
            expr_ref_vector domain_eqs; // additional domain restrictions
            svector<std::pair<app*,func_decl*>> var_diff; // variable differences
            svector<std::pair<app*, unsigned>> var_args; // (uninterpreted) functions in vbody that contain arguments with variables
            q_body(ast_manager& m) : vars(m), mbody(m), vbody(m), domain_eqs(m) {}
        };

        euf::solver&                           ctx;
        solver&                                m_qs;
        ast_manager&                           m;
        stats                                  m_stats;
        model_fixer                            m_model_fixer;
        model_ref                              m_model;
        ref<::solver>                          m_solver;
        scoped_ptr_vector<obj_hashtable<expr>> m_values;
        scoped_ptr_vector<mbp::project_plugin> m_plugins;
        obj_map<quantifier, q_body*>           m_q2body;
        unsigned                               m_max_cex{ 1 };
        vector<std::pair<sat::literal, expr_ref>> m_instantiations;

        void restrict_to_universe(expr * sk, ptr_vector<expr> const & universe);
        // void register_value(expr* e);
        expr_ref replace_model_value(expr* e);
        expr_ref choose_term(euf::enode* r);
        lbool check_forall(quantifier* q);
        q_body* specialize(quantifier* q);
        expr_ref solver_project(model& mdl, q_body& qb, expr_ref_vector& eqs, bool use_inst);
        void add_domain_eqs(model& mdl, q_body& qb);
        void add_domain_bounds(model& mdl, q_body& qb);
        void eliminate_nested_vars(expr_ref_vector& fmls, q_body& qb);
        void extract_var_args(expr* t, q_body& qb);
        void init_model();
        void init_solver();
        mbp::project_plugin* get_plugin(app* var);
        void add_plugin(mbp::project_plugin* p);
        void add_instantiation(sat::literal qlit, expr_ref& proj) {
            TRACE("q", tout << "project: " << proj << "\n";);
            ++m_stats.m_num_instantiations;
            m_instantiations.push_back(std::make_pair(qlit, proj));
        }

    public:

        mbqi(euf::solver& ctx, solver& s);
            
        lbool operator()();

        void init_search();

        void finalize_model(model& mdl);

        void collect_statistics(statistics& st) const;
    };

}
