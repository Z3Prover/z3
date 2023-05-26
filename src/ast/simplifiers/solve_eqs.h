/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    solve_eqs.h

Abstract:

    simplifier for solving equations

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-2.

--*/


#pragma once

#include "util/scoped_ptr_vector.h"
#include "ast/expr_substitution.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/simplifiers/extract_eqs.h"

namespace euf {

    class solve_eqs : public dependent_expr_simplifier {

        friend class solve_context_eqs;

        struct stats {
            unsigned m_num_steps = 0;
            unsigned m_num_elim_vars = 0;
            void reset() {
                m_num_steps = 0;
                m_num_elim_vars = 0;
            }
        };

        struct config {
            bool m_context_solve = true;
            unsigned m_max_occs = UINT_MAX;
        };

        stats                         m_stats;
        config                        m_config;
        th_rewriter                   m_rewriter;
        scoped_ptr_vector<extract_eq> m_extract_plugins;
        unsigned_vector               m_var2id;        // app->get_id() |-> small numeral
        ptr_vector<app>               m_id2var;        // small numeral |-> app
        unsigned_vector               m_id2level;      // small numeral |-> level in substitution ordering
        unsigned_vector               m_subst_ids;     // sorted list of small numeral by level
        vector<dep_eq_vector>         m_next;          // adjacency list for solved equations
        scoped_ptr<expr_substitution> m_subst;         // current substitution
        expr_mark                     m_unsafe_vars;   // expressions that cannot be replaced
        ptr_vector<expr>              m_todo;
        expr_mark                     m_visited;
        obj_map<expr, unsigned>       m_num_occs;


        bool is_var(expr* e) const { return e->get_id() < m_var2id.size() && m_var2id[e->get_id()] != UINT_MAX; }
        unsigned var2id(expr* v) const { return m_var2id[v->get_id()]; }
        bool can_be_var(expr* e) const { return is_uninterp_const(e) && !m_unsafe_vars.is_marked(e) && check_occs(e); }
        void get_eqs(dep_eq_vector& eqs);
        void filter_unsafe_vars();        
        void extract_subst();
        void extract_dep_graph(dep_eq_vector& eqs);
        void normalize();
        void apply_subst(vector<dependent_expr>& old_fmls);
        void save_subst(vector<dependent_expr> const& old_fmls);
        void collect_num_occs(expr * t, expr_fast_mark1 & visited);
        void collect_num_occs();
        bool check_occs(expr* t) const;

    public:

        solve_eqs(ast_manager& m, dependent_expr_state& fmls);

        char const* name() const override { return "solve-eqs"; }

        void reduce() override;

        void updt_params(params_ref const& p) override;

        void collect_param_descrs(param_descrs& r) override;

        void collect_statistics(statistics& st) const override;

        void reset_statistics() override { m_stats.reset(); }

    };
}
