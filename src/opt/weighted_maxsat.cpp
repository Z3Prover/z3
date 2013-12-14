/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    weighted_maxsat.cpp

Abstract:
    Weighted MAXSAT module

Author:

    Anh-Dung Phan (t-anphan) 2013-10-16

Notes:

--*/

#include "weighted_maxsat.h"
#include "smt_theory.h"
#include "smt_context.h"
#include "ast_pp.h"

namespace smt {

    class theory_weighted_maxsat : public theory {
        app_ref_vector           m_vars;       // Auxiliary variables per soft clause
        expr_ref_vector          m_fmls;       // Formulas per soft clause
        app_ref                  m_min_cost_atom; // atom tracking modified lower bound
        bool_var                 m_min_cost_bv;   // max cost Boolean variable
        vector<rational>         m_weights;    // weights of theory variables.
        svector<theory_var>      m_costs;      // set of asserted theory variables
        svector<theory_var>      m_cost_save;  // set of asserted theory variables
        rational                 m_cost;       // current sum of asserted costs
        rational                 m_min_cost;   // current maximal cost assignment.
        u_map<theory_var>        m_bool2var;   // bool_var -> theory_var
        svector<bool_var>        m_var2bool;   // theory_var -> bool_var
        model_ref                m_model;
    public:
        theory_weighted_maxsat(ast_manager& m):
            theory(m.mk_family_id("weighted_maxsat")),
            m_vars(m),
            m_fmls(m),
            m_min_cost_atom(m)
        {}

        /**
           \brief return the complement of variables that are currently assigned.
        */
        void get_assignment(expr_ref_vector& result) {
            result.reset();
            std::sort(m_cost_save.begin(), m_cost_save.end());
            for (unsigned i = 0, j = 0; i < m_vars.size(); ++i) {
                if (j < m_cost_save.size() && m_cost_save[j] == i) {
                    ++j;
                }
                else {
                    result.push_back(m_fmls[i].get());
                }
            }
        }

        virtual void init_search_eh() {
            context & ctx = get_context();
            ast_manager& m = get_manager();
            m_var2bool.reset();
            for (unsigned i = 0; i < m_vars.size(); ++i) {
                app* var = m_vars[i].get();  
                bool_var bv;
                enode* x;
                if (!ctx.e_internalized(var)) {
                    x = ctx.mk_enode(var, false, true, true);
                }
                else {
                    x = ctx.get_enode(var);
                }
                if (ctx.b_internalized(var)) {
                    bv = ctx.get_bool_var(var);
                }
                else {
                    bv = ctx.mk_bool_var(var);
                }
                ctx.set_var_theory(bv, get_id());
                ctx.set_enode_flag(bv, true);
                theory_var v = mk_var(x);
                ctx.attach_th_var(x, this, v);
                m_bool2var.insert(bv, v);
                SASSERT(v == m_var2bool.size());
                m_var2bool.push_back(bv);
                SASSERT(ctx.bool_var2enode(bv));

                lbool asgn = ctx.get_assignment(bv);
                if (asgn == l_true) {
                    assign_eh(bv, true);
                }

            }
            if (m_min_cost_atom) {
                app* var = m_min_cost_atom;
                if (!ctx.e_internalized(var)) {
                    ctx.mk_enode(var, false, true, true);
                }
                if (ctx.b_internalized(var)) {
                    m_min_cost_bv = ctx.get_bool_var(var);
                }
                else {
                    m_min_cost_bv = ctx.mk_bool_var(var);
                }                
                ctx.set_enode_flag(m_min_cost_bv, true);
            }
        }

        void assert_weighted(expr* fml, rational const& w) {
            context & ctx = get_context();
            ast_manager& m = get_manager();
            app_ref var(m), wfml(m);
            var = m.mk_fresh_const("w", m.mk_bool_sort());
            wfml = m.mk_or(var, fml);
            ctx.assert_expr(wfml);
            m_weights.push_back(w);
            m_vars.push_back(var);
            m_fmls.push_back(fml);
            m_min_cost += w;
        }

        rational const& get_min_cost() const { 
            return m_min_cost; 
        }

        expr* set_min_cost(rational const& c) { 
            ast_manager& m = get_manager();
            std::ostringstream strm;
            strm << "cost <= " << c;
            m_min_cost = c; 
            m_min_cost_atom = m.mk_fresh_const(strm.str().c_str(), m.mk_bool_sort());
            return m_min_cost_atom;
        }

        bool found_solution() const {
            return !m_cost_save.empty();
        }

        virtual void assign_eh(bool_var v, bool is_true) {
            IF_VERBOSE(3, verbose_stream() << "Assign " << v << " " << is_true << "\n";);
            if (is_true) {
                context& ctx = get_context();
                theory_var tv = m_bool2var[v];
                rational const& w = m_weights[tv];
                ctx.push_trail(value_trail<context, rational>(m_cost));
                ctx.push_trail(push_back_vector<context, svector<theory_var> >(m_costs));
                m_cost += w;
                m_costs.push_back(tv);
                if (m_cost > m_min_cost) {
                    block(false);
                }
            }
        }

        virtual final_check_status final_check_eh() {
            if (block(true)) {
                return FC_DONE;
            }
            return FC_CONTINUE;
        }

        virtual bool use_diseqs() const { 
            return false;
        }

        virtual bool build_models() const { 
            return false;
        }

        void reset() {
            reset_eh();
        }

        virtual void reset_eh() {
            theory::reset_eh();
            m_vars.reset();
            m_fmls.reset();
            m_weights.reset();
            m_costs.reset();
            m_min_cost.reset();
            m_cost.reset();
            m_cost_save.reset();
            m_bool2var.reset();
            m_var2bool.reset();
            m_min_cost_atom = 0;
            m_model = 0;
        }

        virtual theory * mk_fresh(context * new_ctx) { return alloc(theory_weighted_maxsat, new_ctx->get_manager()); }
        virtual bool internalize_atom(app * atom, bool gate_ctx) { return false; }
        virtual bool internalize_term(app * term) { return false; }
        virtual void new_eq_eh(theory_var v1, theory_var v2) { }
        virtual void new_diseq_eh(theory_var v1, theory_var v2) { }

        void get_model(model_ref& mdl) {
            mdl = m_model.get();
        }

    private:
       
        class compare_cost {
            theory_weighted_maxsat& m_th;
        public:
            compare_cost(theory_weighted_maxsat& t):m_th(t) {}
            bool operator() (theory_var v, theory_var w) const { 
                return m_th.m_weights[v] > m_th.m_weights[w]; 
            }
        };

        bool block(bool is_final) {
            if (m_vars.empty()) {
                return true;
            }
            ast_manager& m = get_manager();
            context& ctx = get_context();
            literal_vector lits;
            compare_cost compare_cost(*this);
            svector<theory_var> costs(m_costs);
            std::sort(costs.begin(), costs.end(), compare_cost);
            rational weight(0);
            for (unsigned i = 0; i < costs.size() && weight < m_min_cost; ++i) {
                weight += m_weights[costs[i]];
                lits.push_back(~literal(m_var2bool[costs[i]]));
            }
            if (m_min_cost_atom) {
                lits.push_back(~literal(m_min_cost_bv));
            }
            IF_VERBOSE(2,
                       verbose_stream() << "block: ";
                       for (unsigned i = 0; i < lits.size(); ++i) {
                           expr_ref tmp(m);
                           ctx.literal2expr(lits[i], tmp);
                           verbose_stream() << tmp << " ";
                       }
                       verbose_stream() << "\n";
                       );

            ctx.mk_th_axiom(get_id(), lits.size(), lits.c_ptr());
            if (is_final && m_cost < m_min_cost) {
                m_min_cost = weight;
                m_cost_save.reset();
                m_cost_save.append(m_costs);
                ctx.get_model(m_model);
            }
            return false;
        }                

    };

}

namespace opt {

    /**
       Iteratively increase cost until there is an assignment during
       final_check that satisfies min_cost.

       Takes: log (n / log(n)) iterations
    */

    static lbool iterative_weighted_maxsat(opt_solver& s, smt::theory_weighted_maxsat& wth) {
        ast_manager& m = s.get_context().get_manager();
        rational cost = wth.get_min_cost();
        rational log_cost(1), tmp(1);
        while (tmp < cost) {
            ++log_cost;
            tmp *= rational(2);
        }
        expr_ref_vector bounds(m);
        expr_ref bound(m);
        lbool result = l_false;
        while (log_cost <= cost && !wth.found_solution() && result != l_undef) {
            std::cout << "cost: " << log_cost << "\n";
            bound = wth.set_min_cost(log_cost);
            bounds.push_back(bound);
            result = s.check_sat_core(1,bounds.c_ptr()+bounds.size()-1);
            log_cost *= rational(2);
        }
        return result;
    }


    struct wmaxsmt::imp {
        ast_manager&     m;
        opt_solver&      s;
        expr_ref_vector  m_soft;
        expr_ref_vector  m_assignment;
        vector<rational> m_weights;
        rational         m_upper;
        rational         m_lower;
        model_ref        m_model;

        imp(ast_manager& m, opt_solver& s, expr_ref_vector& soft_constraints, vector<rational> const& weights):
            m(m), s(s), m_soft(soft_constraints), m_assignment(m), m_weights(weights)
        {}
        ~imp() {}

        smt::theory_weighted_maxsat* get_theory() const {
            smt::context& ctx = s.get_context();                        
            smt::theory_id th_id = m.get_family_id("weighted_maxsat");
            smt::theory* th = ctx.get_theory(th_id);               
            if (th) {
                return dynamic_cast<smt::theory_weighted_maxsat*>(th);
            }
            else {
                return 0;
            }
        }

        smt::theory_weighted_maxsat& ensure_theory() {
            smt::theory_weighted_maxsat* wth = get_theory();
            if (wth) {
                wth->reset();
            }
            else {
                wth = alloc(smt::theory_weighted_maxsat, m);
                s.get_context().register_plugin(wth);
            }
            return *wth;
        }

        /**
           Takes solver with hard constraints added.
           Returns a maximal satisfying subset of weighted soft_constraints
           that are still consistent with the solver state.
        */
        
        lbool operator()() {
            TRACE("opt", tout << "weighted maxsat\n";);
            smt::theory_weighted_maxsat& wth = ensure_theory();
            lbool result;
            {
                solver::scoped_push _s(s);
                for (unsigned i = 0; i < m_soft.size(); ++i) {
                    wth.assert_weighted(m_soft[i].get(), m_weights[i]);
                }
                result = s.check_sat_core(0,0);
                
                wth.get_assignment(m_assignment);
                if (!m_assignment.empty() && result == l_false) {
                    result = l_true;
                }
            }
            m_upper = wth.get_min_cost();
            if (result == l_true) {
                m_lower = m_upper;
            }
            wth.get_model(m_model);
            TRACE("opt", tout << "min cost: " << m_upper << "\n";);
            wth.reset();
            return result;            
        }        

        rational get_lower() const {
            return m_lower;
        }

        rational get_upper() const {
            return m_upper;
        }

        void get_model(model_ref& mdl) {
            mdl = m_model.get();
        }

    };

    wmaxsmt::wmaxsmt(ast_manager& m, opt_solver& s, expr_ref_vector& soft_constraints, vector<rational> const& weights) {
        m_imp = alloc(imp, m, s, soft_constraints, weights);
    }

    wmaxsmt::~wmaxsmt() {
        dealloc(m_imp);
    }
    
    lbool wmaxsmt::operator()() {
        return (*m_imp)();
    }
    rational wmaxsmt::get_lower() const {
        return m_imp->get_lower();
    }
    rational wmaxsmt::get_upper() const {
        return m_imp->get_upper();
    }
    rational wmaxsmt::get_value() const {
        return m_imp->get_upper();
    }
    expr_ref_vector wmaxsmt::get_assignment() const {
        return m_imp->m_assignment;
    }
    void wmaxsmt::set_cancel(bool f) {
        // no-op
    }
    void wmaxsmt::collect_statistics(statistics& st) const {
        // no-op
    }
    void wmaxsmt::get_model(model_ref& mdl) {
        m_imp->get_model(mdl);
    }


    

};

