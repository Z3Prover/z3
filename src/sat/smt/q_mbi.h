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
        euf::solver&                           ctx;
        solver&                                m_qs;
        ast_manager&                           m;
        model_fixer                            m_model_fixer;
        model_ref                              m_model;
        ref<::solver>                          m_solver;
        obj_map<sort, obj_hashtable<expr>*>    m_fresh;
        scoped_ptr_vector<obj_hashtable<expr>> m_values;
        expr_ref_vector                        m_fresh_trail;
        scoped_ptr_vector<mbp::project_plugin> m_plugins;
        unsigned                               m_max_cex{ 1 };

        void restrict_to_universe(expr * sk, ptr_vector<expr> const & universe);
        void register_value(expr* e);
        expr_ref replace_model_value(expr* e);
        expr_ref choose_term(euf::enode* r);
        lbool check_forall(quantifier* q);
        expr_ref specialize(quantifier* q, app_ref_vector& vars);
        expr_ref basic_project(model& mdl, quantifier* q, app_ref_vector& vars);
        expr_ref solver_project(model& mdl, quantifier* q, app_ref_vector& vars);
        expr_ref assign_value(model& mdl, app* v);
        void init_model();
        void init_solver();
        mbp::project_plugin* get_plugin(app* var);
        void add_plugin(mbp::project_plugin* p);

    public:

        mbqi(euf::solver& ctx, solver& s);
            
        lbool operator()();

        void init_search();

        void finalize_model(model& mdl);
    };

}
