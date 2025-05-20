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
    class theory_user_propagator : public theory, public user_propagator::callback {

        struct prop_info {
            ptr_vector<expr>                       m_ids;
            expr_ref                               m_conseq;
            svector<std::pair<expr*, expr*>>       m_eqs;
            literal_vector                         m_lits;
            theory_var                             m_var = null_theory_var;            
            prop_info(unsigned num_fixed, expr* const* fixed_ids,
                      unsigned num_eqs, expr* const* eq_lhs, expr* const* eq_rhs, expr_ref const& c):
                m_ids(num_fixed, fixed_ids),
                m_conseq(c) {
                for (unsigned i = 0; i < num_eqs; ++i)
                    m_eqs.push_back(std::make_pair(eq_lhs[i], eq_rhs[i]));
            }
            
            prop_info(literal_vector const& lits, theory_var v, expr_ref const& val):
                m_conseq(val),
                m_lits(lits),
                m_var(v) {}
                
        };

        struct stats {
            unsigned m_num_propagations;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };

        void*                           m_user_context = nullptr;
        user_propagator::push_eh_t      m_push_eh;
        user_propagator::pop_eh_t       m_pop_eh;
        user_propagator::fresh_eh_t     m_fresh_eh;
        user_propagator::final_eh_t     m_final_eh;
        user_propagator::fixed_eh_t     m_fixed_eh;
        user_propagator::eq_eh_t        m_eq_eh;
        user_propagator::eq_eh_t        m_diseq_eh;
        user_propagator::created_eh_t   m_created_eh;
        user_propagator::decide_eh_t    m_decide_eh;

        user_propagator::context_obj*   m_api_context = nullptr;
        unsigned               m_qhead = 0;
        uint_set               m_fixed;
        vector<prop_info>      m_prop;
        unsigned_vector        m_prop_lim;
        vector<literal_vector> m_id2justification;
        unsigned               m_num_scopes = 0;
        literal_vector         m_lits;
        enode_pair_vector      m_eqs;
        stats                  m_stats;
        expr_ref_vector        m_var2expr;
        unsigned_vector        m_expr2var;
        bool                   m_push_popping;
        expr_ref_vector        m_to_add;
        unsigned_vector        m_to_add_lim;
        unsigned               m_to_add_qhead = 0;
        expr*                  m_next_split_var = nullptr;
        unsigned               m_next_split_idx = 0;
        lbool                  m_next_split_phase = l_undef;
        vector<expr_ref_vector> m_clauses_to_replay;
        unsigned                m_replay_qhead = 0;
        obj_hashtable<expr>   m_add_expr_fresh;

        expr* var2expr(theory_var v) { return m_var2expr.get(v); }
        theory_var expr2var(expr* e) { check_defined(e); return m_expr2var[e->get_id()]; }
        void check_defined(expr* e) {
            if (e->get_id() >= m_expr2var.size() || get_num_vars() <= m_expr2var[e->get_id()])
                throw default_exception("expression is not registered");
        }

        void force_push();

        void propagate_consequence(prop_info const& prop);
        void propagate_new_fixed(prop_info const& prop);
        
        bool_var enode_to_bool(enode* n, unsigned bit);

        void replay_clause(expr_ref_vector const& clause);

    public:
        theory_user_propagator(context& ctx);
        ~theory_user_propagator() override;

        /*
         * \brief initial setup for user propagator.
         */
        void add(
            void*                 ctx, 
            user_propagator::push_eh_t&    push_eh,
            user_propagator::pop_eh_t&     pop_eh,
            user_propagator::fresh_eh_t&   fresh_eh) {
            m_user_context = ctx;
            m_push_eh      = push_eh;
            m_pop_eh       = pop_eh;
            m_fresh_eh     = fresh_eh;
        }

        void add_expr(expr* e, bool ensure_enode);

        void register_final(user_propagator::final_eh_t& final_eh) { m_final_eh = final_eh; }
        void register_fixed(user_propagator::fixed_eh_t& fixed_eh) { m_fixed_eh = fixed_eh; }
        void register_eq(user_propagator::eq_eh_t& eq_eh) { m_eq_eh = eq_eh; }
        void register_diseq(user_propagator::eq_eh_t& diseq_eh) { m_diseq_eh = diseq_eh; }
        void register_created(user_propagator::created_eh_t& created_eh) { m_created_eh = created_eh; }
        void register_decide(user_propagator::decide_eh_t& decide_eh) { m_decide_eh = decide_eh; }

        bool has_fixed() const { return (bool)m_fixed_eh; }
        
        bool propagate_cb(unsigned num_fixed, expr* const* fixed_ids, unsigned num_eqs, expr* const* lhs, expr* const* rhs, expr* conseq) override;
        void register_cb(expr* e) override;
        bool next_split_cb(expr* e, unsigned idx, lbool phase) override;

        void new_fixed_eh(theory_var v, expr* value, unsigned num_lits, literal const* jlits);
        void decide(bool_var& var, bool& is_pos);
        bool get_case_split(bool_var& var, bool& is_pos);

        theory * mk_fresh(context * new_ctx) override;
        char const* get_name() const override { return "user_propagate"; }
        bool internalize_atom(app* atom, bool gate_ctx) override;
        bool internalize_term(app* term) override;
        void new_eq_eh(theory_var v1, theory_var v2) override { if (m_eq_eh) force_push(), m_eq_eh(m_user_context, this, var2expr(v1), var2expr(v2)); }
        void new_diseq_eh(theory_var v1, theory_var v2) override { if (m_diseq_eh) force_push(), m_diseq_eh(m_user_context, this, var2expr(v1), var2expr(v2)); }
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
