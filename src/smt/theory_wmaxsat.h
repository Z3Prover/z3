/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    theory_wmaxsat.h

Abstract:

    Weighted Max-SAT theory plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-05

Notes:

--*/

#ifndef THEORY_WMAXSAT_H_
#define THEORY_WMAXSAT_H_

#include "smt/smt_theory.h"
#include "smt/smt_clause.h"
#include "tactic/generic_model_converter.h"

namespace smt {
    class theory_wmaxsat : public theory {
        struct stats {
            unsigned m_num_blocks;
            unsigned m_num_propagations;
            void reset() { memset(this, 0, sizeof(*this)); }
            stats() { reset(); }
        };        
        generic_model_converter&     m_mc;
        mutable unsynch_mpz_manager m_mpz;
        app_ref_vector           m_vars;        // Auxiliary variables per soft clause
        expr_ref_vector          m_fmls;        // Formulas per soft clause
        vector<rational>         m_rweights;    // weights of theory variables.
        scoped_mpz_vector        m_zweights;
        scoped_mpz_vector        m_old_values;
        svector<theory_var>      m_costs;       // set of asserted theory variables
        unsigned                 m_max_unassigned_index; // index of literal that is not yet assigned and has maximal weight.
        svector<theory_var>      m_sorted_vars; // set of all theory variables, sorted by cost
        svector<theory_var>      m_cost_save;   // set of asserted theory variables
        rational                 m_rmin_cost;   // current maximal cost assignment.
        scoped_mpz               m_zcost;       // current sum of asserted costs
        scoped_mpz               m_zmin_cost;   // current maximal cost assignment.
        bool                     m_found_optimal; 
        u_map<theory_var>        m_bool2var;    // bool_var -> theory_var
        svector<bool_var>        m_var2bool;    // theory_var -> bool_var
        bool                     m_propagate;
        bool                     m_can_propagate;
        bool                     m_normalize; 
        rational                 m_den;         // lcm of denominators for rational weights.
        svector<bool>            m_assigned, m_enabled;
        stats                    m_stats;
    public:
        theory_wmaxsat(ast_manager& m, generic_model_converter& mc);
        ~theory_wmaxsat() override;
        void get_assignment(svector<bool>& result);
        expr* assert_weighted(expr* fml, rational const& w);
        void  disable_var(expr* var);
        bool_var register_var(app* var, bool attach);
        rational get_cost();
        void init_min_cost(rational const& r);

        class numeral_trail : public trail<context> {
            typedef scoped_mpz T;
            T & m_value;
            scoped_mpz_vector&  m_old_values;            
        public:
            numeral_trail(T & value, scoped_mpz_vector& old):
                m_value(value),
                m_old_values(old) {
                old.push_back(value);
            }
            
            ~numeral_trail() override {
            }
            
            void undo(context & ctx) override {
                m_value = m_old_values.back();
                m_old_values.shrink(m_old_values.size() - 1);
            }
        };

        void init_search_eh() override;
        void assign_eh(bool_var v, bool is_true) override;
        final_check_status final_check_eh() override;
        bool use_diseqs() const override {
            return false;
        }
        bool build_models() const override {
            return false;
        }
        void reset_local();
        void reset_eh() override;
        theory * mk_fresh(context * new_ctx) override { return nullptr; }
        bool internalize_atom(app * atom, bool gate_ctx) override { return false; }
        bool internalize_term(app * term) override { return false; }
        void new_eq_eh(theory_var v1, theory_var v2) override { }
        void new_diseq_eh(theory_var v1, theory_var v2) override { }
        void display(std::ostream& out) const override {}
        void restart_eh() override;

        void collect_statistics(::statistics & st) const override {
            st.update("wmaxsat num blocks", m_stats.m_num_blocks);
            st.update("wmaxsat num props", m_stats.m_num_propagations);
        }
        bool can_propagate() override {
            return m_propagate || m_can_propagate;
        }

        void propagate() override;

        bool is_optimal() const;
        expr_ref mk_block();

        

    private:

        void block();
        void propagate(bool_var v);
        void normalize();

        bool max_unassigned_is_blocked();
       
        class compare_cost {
            theory_wmaxsat& m_th;
        public:
            compare_cost(theory_wmaxsat& t):m_th(t) {}
            bool operator() (theory_var v, theory_var w) const { 
                return m_th.m_mpz.gt(m_th.m_zweights[v], m_th.m_zweights[w]); 
            }
        };


    };
};

#endif
