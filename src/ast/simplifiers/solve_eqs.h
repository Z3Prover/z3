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
        struct stats {
            unsigned m_num_steps = 0;
            unsigned m_num_elim_vars = 0;
        };
        struct config {
            bool m_context_solve = true;
            unsigned m_max_occs = UINT_MAX;
        };

        th_rewriter                   m_rewriter;
        scoped_ptr_vector<extract_eq> m_extract_plugins;
        unsigned_vector               m_var2id, m_id2level, m_subst_ids;
        ptr_vector<app>               m_id2var;
        vector<dep_eq_vector>         m_next;  
        scoped_ptr<expr_substitution> m_subst;

        expr_mark                     m_unsafe_vars;   // expressions that cannot be replaced
        stats                         m_stats;
        config                        m_config;

        void add_subst(dependent_eq const& eq);

        bool is_var(expr* e) const { return e->get_id() < m_var2id.size() && m_var2id[e->get_id()] != UINT_MAX; }
        unsigned var2id(expr* v) const { return m_var2id[v->get_id()]; }

        void get_eqs(dep_eq_vector& eqs) {
            for (unsigned i = m_qhead; i < m_fmls.size(); ++i) 
                get_eqs(m_fmls[i], eqs);            
        }

        void get_eqs(dependent_expr const& f, dep_eq_vector& eqs) {
            for (extract_eq* ex : m_extract_plugins)
                ex->get_eqs(f, eqs);
        }

        void filter_unsafe_vars();
        bool can_be_var(expr* e) const { return is_uninterp_const(e) && !m_unsafe_vars.is_marked(e); }
        void extract_subst();
        void extract_dep_graph(dep_eq_vector& eqs);
        void normalize();
        void apply_subst();
        void save_subst();

    public:

        solve_eqs(ast_manager& m, dependent_expr_state& fmls);

        void push() override { dependent_expr_simplifier::push(); }
        void pop(unsigned n) override { dependent_expr_simplifier::pop(n); }
        void reduce() override;

        void updt_params(params_ref const& p) override;
        void collect_statistics(statistics& st) const override;
    };
}
