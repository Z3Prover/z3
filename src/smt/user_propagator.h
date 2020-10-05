/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    user_propagator.h

Abstract:

    User-propagator plugin.
    Adds user plugins to propagate based on 
    terms receiving fixed values or equalities.

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-17

Notes:


--*/

#pragma once

#include "util/uint_set.h"
#include "smt/smt_theory.h"
#include "solver/solver.h"

namespace smt {
    class user_propagator : public theory, public solver::propagate_callback {

        struct prop_info {
            unsigned_vector m_ids;
            expr_ref        m_conseq;
            svector<std::pair<unsigned, unsigned>> m_eqs;
            prop_info(unsigned num_fixed, unsigned const* fixed_ids, unsigned num_eqs, unsigned const* eq_lhs, unsigned const* eq_rhs, expr_ref const& c):
                m_ids(num_fixed, fixed_ids),
                m_conseq(c)
            {
                for (unsigned i = 0; i < num_eqs; ++i)
                    m_eqs.push_back(std::make_pair(eq_lhs[i], eq_rhs[i]));
            }
        };

        struct stats {
            unsigned m_num_propagations;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };

        void*                  m_user_context;
        solver::push_eh_t      m_push_eh;
        solver::pop_eh_t       m_pop_eh;
        solver::fresh_eh_t     m_fresh_eh;
        solver::final_eh_t     m_final_eh;
        solver::fixed_eh_t     m_fixed_eh;
        solver::eq_eh_t        m_eq_eh;
        solver::eq_eh_t        m_diseq_eh;
        solver::context_obj*   m_api_context { nullptr };
        unsigned               m_qhead { 0 };
        uint_set               m_fixed;
        vector<prop_info>      m_prop;
        unsigned_vector        m_prop_lim;
        vector<literal_vector> m_id2justification;
        unsigned               m_num_scopes { 0 };
        literal_vector         m_lits;
        enode_pair_vector      m_eqs;
        stats                  m_stats;

        void force_push();

    public:
        user_propagator(context& ctx);
        
        ~user_propagator() override;

        /*
         * \brief initial setup for user propagator.
         */
        void add(
            void*                 ctx, 
            solver::push_eh_t&    push_eh,
            solver::pop_eh_t&     pop_eh,
            solver::fresh_eh_t&   fresh_eh) {
            m_user_context = ctx;
            m_push_eh      = push_eh;
            m_pop_eh       = pop_eh;
            m_fresh_eh     = fresh_eh;
        }

        unsigned add_expr(expr* e);

        void register_final(solver::final_eh_t& final_eh) { m_final_eh = final_eh; }
        void register_fixed(solver::fixed_eh_t& fixed_eh) { m_fixed_eh = fixed_eh; }
        void register_eq(solver::eq_eh_t& eq_eh) { m_eq_eh = eq_eh; }
        void register_diseq(solver::eq_eh_t& diseq_eh) { m_diseq_eh = diseq_eh; }

        bool has_fixed() const { return (bool)m_fixed_eh; }

        void propagate_cb(unsigned num_fixed, unsigned const* fixed_ids, unsigned num_eqs, unsigned const* lhs, unsigned const* rhs, expr* conseq) override;

        void new_fixed_eh(theory_var v, expr* value, unsigned num_lits, literal const* jlits);

        theory * mk_fresh(context * new_ctx) override;
        bool internalize_atom(app * atom, bool gate_ctx) override { UNREACHABLE(); return false; }
        bool internalize_term(app * term) override { UNREACHABLE(); return false; }
        void new_eq_eh(theory_var v1, theory_var v2) override { if (m_eq_eh) m_eq_eh(m_user_context, this, v1, v2); }
        void new_diseq_eh(theory_var v1, theory_var v2) override { if (m_diseq_eh) m_diseq_eh(m_user_context, this, v1, v2); }
        bool use_diseqs() const override { return ((bool)m_diseq_eh); }
        bool build_models() const override { return false; }
        final_check_status final_check_eh() override;
        void reset_eh() override {}
        void assign_eh(bool_var v, bool is_true) override { }
        void init_search_eh() override {}
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        void restart_eh() override {}
        void collect_statistics(::statistics & st) const override;
        model_value_proc * mk_value(enode * n, model_generator & mg) override { return nullptr; }
        void init_model(model_generator & m) override {}
        bool include_func_interp(func_decl* f) override { return false; }
        bool can_propagate() override;
        void propagate() override; 
        void display(std::ostream& out) const override {}
    };
};
