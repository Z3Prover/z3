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

namespace smt {

    class theory_weighted_maxsat : public theory {
        expr_ref_vector          m_vars;
        expr_ref_vector          m_fmls;
        vector<rational>         m_weights;    // weights of theory variables.
        svector<theory_var>      m_costs;      // set of asserted theory variables
        rational                 m_cost;       // current sum of asserted costs
        rational                 m_min_cost;   // current minimal cost assignment.
        svector<theory_var>      m_assignment; // current best assignment.
    public:
        theory_weighted_maxsat(ast_manager& m):
            theory(m.get_family_id("weighted_maxsat")),
            m_vars(m),
            m_fmls(m)
        {}

        void get_assignment(expr_ref_vector& result) {
            result.reset();
            for (unsigned i = 0; i < m_assignment.size(); ++i) {
                result.push_back(m_fmls[m_assignment[i]].get());
            }
        }

        void assert_weighted(expr* fml, rational const& w) {
            context & ctx = get_context();
            ast_manager& m = get_manager();
            expr_ref var(m);
            var = m.mk_fresh_const("w", m.mk_bool_sort());
            ctx.internalize(fml, false);  // TBD: assume or require simplification?
            ctx.internalize(var, false);
            enode* x, *y;
            x = ctx.get_enode(fml);
            y = ctx.get_enode(var);
            theory_var v = mk_var(y);
            SASSERT(v == m_vars.size());
            SASSERT(v == m_weights.size());
            m_vars.push_back(var);
            m_fmls.push_back(fml);
            ctx.attach_th_var(y, this, v);
            literal lx(ctx.get_bool_var(fml));
            literal ly(ctx.get_bool_var(var));
            ctx.mk_th_axiom(get_id(), lx, ly);
            m_weights.push_back(w);
            m_min_cost += w;
        }

        virtual void assign_eh(bool_var v, bool is_true) {
            if (is_true) {
                context& ctx = get_context();
                rational const& w = m_weights[v];
                ctx.push_trail(value_trail<context, rational>(m_cost));
                ctx.push_trail(push_back_vector<context, svector<theory_var> >(m_costs));
                m_cost += w;
                m_costs.push_back(v);
                if (m_cost > m_min_cost) {
                    block();
                }
            }
        }

        virtual final_check_status final_check_eh() {
            if (m_cost < m_min_cost) {
                m_min_cost = m_cost;
                m_assignment.reset();
                m_assignment.append(m_costs);
            }
            block();
            return FC_DONE;
        }

        virtual void reset_eh() {
            theory::reset_eh();
            m_vars.reset();
            m_weights.reset();
            m_costs.reset();
            m_cost.reset();
            m_min_cost.reset();
            m_assignment.reset();
        }

        virtual theory * mk_fresh(context * new_ctx) { UNREACHABLE(); return 0;} // TBD
        virtual bool internalize_atom(app * atom, bool gate_ctx) { return false; }
        virtual bool internalize_term(app * term) { return false; }
        virtual void new_eq_eh(theory_var v1, theory_var v2) { UNREACHABLE(); }
        virtual void new_diseq_eh(theory_var v1, theory_var v2) { UNREACHABLE(); }


    private:
       
        class compare_cost {
            theory_weighted_maxsat& m_th;
        public:
            compare_cost(theory_weighted_maxsat& t):m_th(t) {}
            bool operator() (theory_var v, theory_var w) const { 
                return m_th.m_weights[v] < m_th.m_weights[w]; 
            }
        };

        void block() {
            ast_manager& m = get_manager();
            context& ctx = get_context();
            literal_vector lits;
            compare_cost compare_cost(*this);
            svector<theory_var> costs(m_costs);
            std::sort(costs.begin(), costs.end(), compare_cost);
            rational weight(0);
            for (unsigned i = 0; i < costs.size() && weight < m_min_cost; ++i) {
                weight += m_weights[costs[i]];
                lits.push_back(~literal(costs[i]));
            }
            justification * js = 0;
            if (m.proofs_enabled()) {
                js = new (ctx.get_region()) 
                    theory_lemma_justification(get_id(), ctx, lits.size(), lits.c_ptr());
            }
            ctx.mk_clause(lits.size(), lits.c_ptr(), js, CLS_AUX_LEMMA, 0);
        }        
    };

}

namespace opt {


    /**
       Takes solver with hard constraints added.
       Returns a maximal satisfying subset of weighted soft_constraints
       that are still consistent with the solver state.
    */
    
    lbool weighted_maxsat(opt_solver& s, expr_ref_vector& soft_constraints, vector<rational> const& weights) {
        ast_manager& m = soft_constraints.get_manager();
        smt::context& ctx = s.get_context();                        
        smt::theory_id th_id = m.get_family_id("weighted_maxsat");
        smt::theory* th = ctx.get_theory(th_id);               
        if (!th) {
            th = alloc(smt::theory_weighted_maxsat, m);
            ctx.register_plugin(th);
        }
        smt::theory_weighted_maxsat* wth = dynamic_cast<smt::theory_weighted_maxsat*>(th);
        for (unsigned i = 0; i < soft_constraints.size(); ++i) {
            wth->assert_weighted(soft_constraints[i].get(), weights[i]);
        }
        lbool result = s.check_sat_core(0,0);
        wth->get_assignment(soft_constraints);
        if (!soft_constraints.empty() && result == l_false) {
            result = l_true;
        }
        return result;
    }
};

