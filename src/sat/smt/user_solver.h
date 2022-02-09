/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    user_solver.h

Abstract:

    User-propagator plugin.
    Adds user plugins to propagate based on 
    terms receiving fixed values or equalities.

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-17

--*/

#pragma once

#include "sat/smt/sat_th.h"
#include "solver/solver.h"
#include "tactic/user_propagator_base.h"


namespace user_solver {

    class solver : public euf::th_euf_solver, public user_propagator::callback {

        struct prop_info {
            unsigned_vector  m_ids;
            expr_ref         m_conseq;
            svector<std::pair<expr*, expr*>> m_eqs;
            sat::literal_vector                    m_lits;
            euf::theory_var                  m_var = euf::null_theory_var;

            prop_info(unsigned num_fixed, unsigned const* fixed_ids, unsigned num_eqs, expr* const* eq_lhs, expr* const* eq_rhs, expr_ref const& c):
                m_ids(num_fixed, fixed_ids),
                m_conseq(c)
            {
                for (unsigned i = 0; i < num_eqs; ++i)
                    m_eqs.push_back(std::make_pair(eq_lhs[i], eq_rhs[i]));
            }

            prop_info(sat::literal_vector const& lits, euf::theory_var v, expr_ref const& val):
                m_conseq(val),
                m_lits(lits),
                m_var(v) {}

        };

        struct stats {
            unsigned m_num_propagations;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };

        void*                  m_user_context;
        user_propagator::push_eh_t      m_push_eh;
        user_propagator::pop_eh_t       m_pop_eh;
        user_propagator::fresh_eh_t     m_fresh_eh;
        user_propagator::final_eh_t     m_final_eh;
        user_propagator::fixed_eh_t     m_fixed_eh;
        user_propagator::eq_eh_t        m_eq_eh;
        user_propagator::eq_eh_t        m_diseq_eh;
        user_propagator::created_eh_t   m_created_eh;
        user_propagator::context_obj*   m_api_context = nullptr;
        unsigned               m_qhead = 0;
        vector<prop_info>      m_prop;
        unsigned_vector        m_prop_lim;
        vector<sat::literal_vector> m_id2justification;
        sat::literal_vector         m_lits;
        euf::enode_pair_vector      m_eqs;
        unsigned_vector             m_fixed_ids;
        stats                  m_stats;

        struct justification {
            unsigned m_propagation_index { 0 };

            justification(unsigned prop_index): m_propagation_index(prop_index) {}

            sat::ext_constraint_idx to_index() const { 
                return sat::constraint_base::mem2base(this); 
            }
            static justification& from_index(size_t idx) {
                return *reinterpret_cast<justification*>(sat::constraint_base::from_index(idx)->mem());
            }
            static size_t get_obj_size() { return sat::constraint_base::obj_size(sizeof(justification)); }
        };

        sat::justification mk_justification(unsigned propagation_index);

        void propagate_consequence(prop_info const& prop);
        void propagate_new_fixed(prop_info const& prop);

	void validate_propagation();

        bool visit(expr* e) override;
        bool visited(expr* e) override;
        bool post_visit(expr* e, bool sign, bool root) override;

    public:
        solver(euf::solver& ctx);
        
        ~solver() override;

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

        void add_expr(expr* e);

        void register_final(user_propagator::final_eh_t& final_eh) { m_final_eh = final_eh; }
        void register_fixed(user_propagator::fixed_eh_t& fixed_eh) { m_fixed_eh = fixed_eh; }
        void register_eq(user_propagator::eq_eh_t& eq_eh) { m_eq_eh = eq_eh; }
        void register_diseq(user_propagator::eq_eh_t& diseq_eh) { m_diseq_eh = diseq_eh; }
        void register_created(user_propagator::created_eh_t& created_eh) { m_created_eh = created_eh; }

        bool has_fixed() const { return (bool)m_fixed_eh; }

        void propagate_cb(unsigned num_fixed, expr* const* fixed_ids, unsigned num_eqs, expr* const* lhs, expr* const* rhs, expr* conseq) override;
        void register_cb(expr* e) override;

        void new_fixed_eh(euf::theory_var v, expr* value, unsigned num_lits, sat::literal const* jlits);

        void asserted(sat::literal lit) override;
        sat::check_result check() override;
        void push_core() override;
        void pop_core(unsigned n) override;
        bool unit_propagate() override;
        void get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector & r, bool probing) override;
        void collect_statistics(statistics& st) const override;
        sat::literal internalize(expr* e, bool sign, bool root, bool learned) override;
        void internalize(expr* e, bool redundant) override;
        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override;
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override;
        euf::th_solver* clone(euf::solver& ctx) override;

    };
};
