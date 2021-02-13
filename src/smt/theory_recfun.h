/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    theory_recfun.h

Abstract:

    Theory responsible for unrolling recursive functions

Author:

    Simon Cruanes December 2017

Revision History:

--*/
#pragma once

#include "smt/smt_theory.h"
#include "smt/smt_context.h"
#include "ast/ast_pp.h"
#include "ast/recfun_decl_plugin.h"

namespace smt {

    class theory_recfun : public theory {
        struct stats {
            unsigned m_case_expansions, m_body_expansions, m_macro_expansions;
            void reset() { memset(this, 0, sizeof(stats)); }
            stats() { reset(); }
        };
        
        recfun::decl::plugin&   m_plugin;
        recfun::util&           m_util;
        stats                   m_stats;

        // book-keeping for depth of predicates
        expr_ref_vector          m_disabled_guards;
        expr_ref_vector          m_enabled_guards;
        obj_map<expr, expr_ref_vector*> m_guard2pending;
        obj_map<expr, unsigned>  m_pred_depth;
        expr_ref_vector          m_preds;
        unsigned_vector          m_preds_lim;
        unsigned                 m_num_rounds { 0 };

        ptr_vector<recfun::case_expansion> m_q_case_expand;
        ptr_vector<recfun::body_expansion> m_q_body_expand;
        vector<literal_vector>     m_q_clauses;
        ptr_vector<expr>           m_q_guards;

        bool is_enabled_guard(expr* guard) { expr_ref ng(m.mk_not(guard), m); return m_enabled_guards.contains(ng); }
        bool is_disabled_guard(expr* guard) { return m_disabled_guards.contains(guard); }

        recfun::util & u() const { return m_util; }
        bool is_defined(app * f) const { return u().is_defined(f); }
        bool is_case_pred(app * f) const { return u().is_case_pred(f); }

        bool is_defined(enode * e) const { return is_defined(e->get_owner()); }
        bool is_case_pred(enode * e) const { return is_case_pred(e->get_owner()); }

        void activate_guard(expr* guard, expr_ref_vector const& guards);

        void reset_queues();
        expr_ref apply_args(unsigned depth, recfun::vars const & vars, expr_ref_vector const & args, expr * e); //!< substitute variables by args
        void assert_macro_axiom(recfun::case_expansion & e);
        void assert_case_axioms(recfun::case_expansion & e);
        void assert_body_axiom(recfun::body_expansion & e);
        literal mk_literal(expr* e);

        void disable_guard(expr* guard, expr_ref_vector const& guards);
        unsigned get_depth(expr* e);
        void set_depth(unsigned d, expr* e);
        void set_depth_rec(unsigned d, expr* e);
        
        literal mk_eq_lit(expr* l, expr* r);
        bool is_standard_order(recfun::vars const& vars) const { 
            return vars.empty() || vars[vars.size()-1]->get_idx() == 0;
        }
    protected:
        void push_case_expand(recfun::case_expansion* e) { m_q_case_expand.push_back(e); }
        void push_body_expand(recfun::body_expansion* e) { m_q_body_expand.push_back(e); }

        bool internalize_atom(app * atom, bool gate_ctx) override;
        bool internalize_term(app * term) override;
        void reset_eh() override;
        void relevant_eh(app * n) override;
        char const * get_name() const override;
        final_check_status final_check_eh() override;
        void assign_eh(bool_var v, bool is_true) override;
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        void restart_eh() override;
        bool can_propagate() override;
        void propagate() override;
        bool should_research(expr_ref_vector &) override;

        void new_eq_eh(theory_var v1, theory_var v2) override {}
        void new_diseq_eh(theory_var v1, theory_var v2) override {}
        void add_theory_assumptions(expr_ref_vector & assumptions) override;

    public:
        theory_recfun(context& ctx);
        ~theory_recfun() override;
        theory * mk_fresh(context * new_ctx) override;
        void init_search_eh() override;
        void display(std::ostream & out) const override;
        void collect_statistics(::statistics & st) const override;
    };
}

