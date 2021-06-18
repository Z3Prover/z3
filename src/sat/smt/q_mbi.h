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
            unsigned m_num_checks;
            
            stats() { reset(); }

            void reset() {
                memset(this, 0, sizeof(*this));
            }
        };
        struct q_body {
            app_ref_vector  vars;
            bool_vector     free_vars;  // variables that occur in positive equalities
            expr_ref        mbody;      // body specialized with respect to model
            expr_ref_vector vbody;      // (negation of) body specialized with respect to vars
            expr_ref_vector domain_eqs; // additional domain restrictions

            svector<std::pair<app*, unsigned>> var_args;   // (uninterpreted) functions in vbody that contain arguments with variables
            q_body(ast_manager& m) : vars(m), mbody(m), vbody(m), domain_eqs(m) {}
            void set_free(unsigned idx) { free_vars.setx(idx, true, false); }
            bool is_free(unsigned idx) const { return free_vars.get(idx, false); }
            bool is_free(expr* e) const { return is_var(e) && is_free(to_var(e)->get_idx()); }
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
        unsigned                               m_max_quick_check_rounds { 100 };
        unsigned                               m_max_unbounded_equalities { 10 };
        unsigned                               m_max_choose_candidates { 10 };
        unsigned                               m_generation_bound{ UINT_MAX };
        unsigned                               m_generation_max { UINT_MAX };
        typedef std::tuple<sat::literal, expr_ref, unsigned> instantiation_t;
        vector<instantiation_t> m_instantiations;

        void restrict_to_universe(expr * sk, ptr_vector<expr> const & universe);
        // void register_value(expr* e);
        expr_ref replace_model_value(expr* e);
        expr_ref choose_term(euf::enode* r);
        lbool check_forall(quantifier* q);
        q_body* specialize(quantifier* q);
        q_body* q2body(quantifier* q);
        expr_ref solver_project(model& mdl, q_body& qb, expr_ref_vector& eqs, bool use_inst);
        void add_universe_restriction(quantifier* q, q_body& qb);
        void add_domain_eqs(model& mdl, q_body& qb);
        void add_domain_bounds(model& mdl, q_body& qb);
        void eliminate_nested_vars(expr_ref_vector& fmls, q_body& qb);
        void extract_var_args(expr* t, q_body& qb);
        void extract_free_vars(quantifier* q, q_body& qb);
        void init_model();
        void init_solver();
        mbp::project_plugin* get_plugin(app* var);
        void add_plugin(mbp::project_plugin* p);
        void add_instantiation(quantifier* q, expr_ref& proj);

        bool check_forall_default(quantifier* q, q_body& qb, model& mdl);
        bool check_forall_subst(quantifier* q, q_body& qb, model& mdl);

        bool quick_check(quantifier* q, quantifier* q_flat, q_body& qb);
        bool next_offset(unsigned_vector& offsets, app_ref_vector const& vars);
        bool first_offset(unsigned_vector& offsets, app_ref_vector const& vars);
        bool next_offset(unsigned_vector& offsets, app_ref_vector const& vars, unsigned i, unsigned start);
        void set_binding(unsigned_vector const& offsets, app_ref_vector const& vars, expr_ref_vector& binding);

    public:

        mbqi(euf::solver& ctx, solver& s);
            
        lbool operator()();

        void init_search();

        void finalize_model(model& mdl);

        void collect_statistics(statistics& st) const;
    };

}
