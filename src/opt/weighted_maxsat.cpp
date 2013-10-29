/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    weighted_maxsat.h

Abstract:
    Weighted MAXSAT module

Author:

    Anh-Dung Phan (t-anphan) 2013-10-16

Notes:

--*/

#include "weighted_maxsat.h"
#include "smt_theory.h"
#include "smt_context.h"

namespace opt {

    class theory_weighted_maxsat : public smt::theory {
        vector<rational>         m_weights;    // weights of theory variables.
        svector<smt::theory_var> m_costs;      // set of asserted theory variables
        rational                 m_cost;       // current sum of asserted costs
        rational                 m_min_cost;   // current minimal cost assignment.
        svector<smt::theory_var> m_assignment; // current best assignment.
    public:
        theory_weighted_maxsat(ast_manager& m):
            theory(m.get_family_id("weighted_maxsat"))
        {}

        void assert_weighted(expr* fml, rational const& w) {
            smt::bool_var v = smt::null_theory_var;
            // internalize fml
            // assert weighted clause. v \/ fml
            // 
            m_weights.push_back(w);
            m_min_cost += w;
        }

        virtual void assign_eh(smt::bool_var v, bool is_true) {
            smt::context& ctx = get_context();
            if (is_true) {
                rational const& w = m_weights[v];
                ctx.push_trail(value_trail<smt::context, rational>(m_cost));
                // TBD: ctx.push_trail(...trail.pop_back(m_costly));
                m_cost += w;
                m_costs.push_back(v);
                if (m_cost > m_min_cost) {
                    block();
                }
            }
        }

        virtual smt::final_check_status final_check_eh() {
            if (m_cost < m_min_cost) {
                m_min_cost = m_cost;
                m_assignment.reset();
                m_assignment.append(m_costs);
            }
            block();
            return smt::FC_DONE;
        }

    private:
       
        class compare_cost {
            theory_weighted_maxsat& m_th;
        public:
            compare_cost(theory_weighted_maxsat& t):m_th(t) {}
            bool operator() (smt::theory_var v, smt::theory_var w) const { 
                return m_th.m_weights[v] < m_th.m_weights[w]; 
            }
        };

        void block() {
            ast_manager& m = get_manager();
            smt::context& ctx = get_context();
            smt::literal_vector lits;
            compare_cost compare_cost(*this);
            std::sort(m_costs.begin(), m_costs.end(), compare_cost);
            rational weight(0);
            for (unsigned i = 0; i < m_costs.size() && 
                     weight < m_min_cost; ++i) {
                weight += m_weights[m_costs[i]];
                lits.push_back(~smt::literal(m_costs[i]));
            }
            smt::justification * js = 0;
            if (m.proofs_enabled()) {
                js = new (ctx.get_region()) 
                    smt::theory_lemma_justification(get_id(), ctx, lits.size(), lits.c_ptr());
            }
            ctx.mk_clause(lits.size(), lits.c_ptr(), js, smt::CLS_AUX_LEMMA, 0);
        }        
    };

    /**
       Takes solver with hard constraints added.
       Returns a maximal satisfying subset of weighted soft_constraints
       that are still consistent with the solver state.
    */
    
    lbool weighted_maxsat(solver& s, expr_ref_vector& soft_constraints, vector<rational> const& weights) {
        NOT_IMPLEMENTED_YET();
        return l_false;
    }
};

