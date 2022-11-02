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

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/rewriter/th_rewriter.h"


namespace euf {

    struct dependent_eq {
        app* var;
        expr_ref term;
        expr_dependency* dep;
        dependent_eq(app* var, expr_ref& term, expr_dependency* d) : var(var), term(term), dep(d) {}
    };

    typedef vector<dependent_eq> dep_eq_vector;

    class extract_eq {
    pulic:
        virtual ~extract_eq() {}
        virtual void get_eqs(depdendent_expr const& e, dep_eq_vector& eqs) = 0;
    };

    class solve_eqs : public dependent_expr_simplifier {
        th_rewriter                   m_rewriter;
        scoped_ptr_vector<extract_eq> m_extract_plugins;
        unsigned_vector               m_var2id;
        ptr_vector<app>               m_id2var;
        vector<uint_set>              m_next;

        void init();

        bool is_var(expr* v) const;
        unsigned var2id(expr* v) const { return m_var2id[v->get_id()]; }

        void get_eqs(dep_eq_vector& eqs) {
            for (unsigned i = m_qhead; i < m_fmls.size(); ++i) 
                get_eqs(m_fmls[i](), eqs);            
        }

        void get_eqs(dependent_expr const& f, dep_eq_vector& eqs) {
            for (auto* ex : m_extract_plugins)
                ex->get_eqs(f, eqs);
        }

        void extract_subst(dep_eq_vector& eqs, dep_eq_vector& subst);
        void apply_subst();

    public:

        solve_eqs(ast_manager& m, dependent_expr_state& fmls) : dependent_expr_simplifier(m, fmls), m_rewriter(m) {}

        void push() override { dependent_expr_simplifier::push(); }
        void pop(unsigned n) override { dependent_expr_simplifier::pop(n); }
        void reduce() override;
    };
}
