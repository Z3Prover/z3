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
        opt::opt_solver&         s;
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
        bool                     m_propagate;  
        svector<bool>            m_assigned;

    public:
        theory_weighted_maxsat(ast_manager& m, opt::opt_solver& s):
            theory(m.mk_family_id("weighted_maxsat")),
            s(s),
            m_vars(m),
            m_fmls(m),
            m_min_cost_atom(m),
            m_propagate(false)
        {}

        /**
           \brief return the complement of variables that are currently assigned.
        */
        void get_assignment(svector<bool>& result) {
            result.reset();

            std::sort(m_cost_save.begin(), m_cost_save.end());
            for (unsigned i = 0, j = 0; i < m_vars.size(); ++i) {
                if (j < m_cost_save.size() && m_cost_save[j] == i) {
                    result.push_back(false);
                    ++j;
                }
                else {
                    result.push_back(true);
                }
            }
            TRACE("opt",
                  tout << "cost save: ";
                  for (unsigned i = 0; i < m_cost_save.size(); ++i) {
                      tout << m_cost_save[i] << " ";
                  }
                  tout << "\nvars: ";
                  for (unsigned i = 0; i < m_vars.size(); ++i) {
                      tout << mk_pp(m_vars[i].get(), get_manager()) << " ";
                  }
                  tout << "\nassignment";
                  for (unsigned i = 0; i < result.size(); ++i) {
                      tout << result[i] << " ";
                  }
                  tout << "\n";);                  

        }

        virtual void init_search_eh() {
            context & ctx = get_context();
            ast_manager& m = get_manager();
            bool initialized = !m_var2bool.empty();
            m_propagate = true;

            for (unsigned i = 0; !initialized && i < m_vars.size(); ++i) {
                app* var = m_vars[i].get();  
                bool_var bv;
                theory_var v;
                SASSERT(!ctx.e_internalized(var));
                enode* x = ctx.mk_enode(var, false, true, true);
                if (ctx.b_internalized(var)) {
                    bv = ctx.get_bool_var(var);
                }
                else {
                    bv = ctx.mk_bool_var(var);
                }
                ctx.set_var_theory(bv, get_id());                    
                ctx.set_enode_flag(bv, true);
                v = mk_var(x);
                ctx.attach_th_var(x, this, v);
                m_bool2var.insert(bv, v);
                SASSERT(v == m_var2bool.size());
                SASSERT(i == v);
                m_var2bool.push_back(bv);
                SASSERT(ctx.bool_var2enode(bv));
            }

            if (!initialized && m_min_cost_atom) {
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
            s.mc().insert(var->get_decl());
            wfml = m.mk_or(var, fml);
            ctx.assert_expr(wfml);
            m_weights.push_back(w);
            m_vars.push_back(var);
            m_fmls.push_back(fml);
            m_assigned.push_back(false);
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
            s.mc().insert(m_min_cost_atom->get_decl());
            return m_min_cost_atom;
        }

        bool found_solution() const {
            return !m_cost_save.empty();
        }

        virtual void assign_eh(bool_var v, bool is_true) {
            TRACE("opt", tout << "Assign " << mk_pp(m_vars[m_bool2var[v]].get(), get_manager()) << " " << is_true << "\n";);
            if (is_true) {
                context& ctx = get_context();
                theory_var tv = m_bool2var[v];
                if (m_assigned[tv]) return;
                rational const& w = m_weights[tv];
                ctx.push_trail(value_trail<context, rational>(m_cost));
                ctx.push_trail(push_back_vector<context, svector<theory_var> >(m_costs));
                ctx.push_trail(value_trail<context, bool>(m_assigned[tv]));
                m_cost += w;
                m_costs.push_back(tv);
                m_assigned[tv] = true;
                if (m_cost > m_min_cost) {
                    block();
                }
            }
        }

        virtual final_check_status final_check_eh() {
            return FC_DONE;
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
            m_propagate = false;
            m_assigned.reset();
        }

        virtual theory * mk_fresh(context * new_ctx) { return 0; }
        virtual bool internalize_atom(app * atom, bool gate_ctx) { return false; }
        virtual bool internalize_term(app * term) { return false; }
        virtual void new_eq_eh(theory_var v1, theory_var v2) { }
        virtual void new_diseq_eh(theory_var v1, theory_var v2) { }

        virtual bool can_propagate() {
            return m_propagate;
        }

        virtual void propagate() {
            context& ctx = get_context();
            for (unsigned i = 0; m_propagate && i < m_vars.size(); ++i) {
                bool_var bv = m_var2bool[i];
                lbool asgn = ctx.get_assignment(bv);
                if (asgn == l_true) {
                    assign_eh(bv, true);
                }
            }
            m_propagate = false;
        }
        


        bool is_optimal() const {
            return m_cost < m_min_cost;
        }

        expr_ref mk_block() {
            ast_manager& m = get_manager();
            expr_ref_vector disj(m);
            compare_cost compare_cost(*this);
            svector<theory_var> costs(m_costs);
            std::sort(costs.begin(), costs.end(), compare_cost);
            rational weight(0);
            for (unsigned i = 0; i < costs.size() && weight < m_min_cost; ++i) {
                weight += m_weights[costs[i]];
                disj.push_back(m.mk_not(m_vars[costs[i]].get()));
            }
            if (m_min_cost_atom) {
                disj.push_back(m.mk_not(m_min_cost_atom));
            }
            if (is_optimal()) {
                IF_VERBOSE(1, verbose_stream() << "(wmaxsat with lower bound: " << weight << "\n";);
                m_min_cost = weight;
                m_cost_save.reset();
                m_cost_save.append(m_costs);
            }

            expr_ref result(m.mk_or(disj.size(), disj.c_ptr()), m);

            TRACE("opt",
                  tout << result << "\n";
                  if (is_optimal()) {
                      tout << "costs: ";
                      for (unsigned i = 0; i < m_costs.size(); ++i) {
                          tout << mk_pp(get_enode(m_costs[i])->get_owner(), get_manager()) << " ";
                      }
                      tout << "\n";
                      get_context().display(tout);                      
                  });
            return result;
        }


    private:

        void block() {
            if (m_vars.empty()) {
                return;
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
            TRACE("opt",
                  tout << "block: ";
                  for (unsigned i = 0; i < lits.size(); ++i) {
                      expr_ref tmp(m);
                      ctx.literal2expr(lits[i], tmp);
                      tout << tmp << " ";
                  }
                  tout << "\n";
                  );

            ctx.mk_th_axiom(get_id(), lits.size(), lits.c_ptr());
        }                

       
        class compare_cost {
            theory_weighted_maxsat& m_th;
        public:
            compare_cost(theory_weighted_maxsat& t):m_th(t) {}
            bool operator() (theory_var v, theory_var w) const { 
                return m_th.m_weights[v] > m_th.m_weights[w]; 
            }
        };


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
        svector<bool>    m_assignment;
        vector<rational> m_weights;
        rational         m_upper;
        rational         m_lower;
        model_ref        m_model;

        imp(ast_manager& m, opt_solver& s, expr_ref_vector& soft_constraints, vector<rational> const& weights):
            m(m), s(s), m_soft(soft_constraints), m_weights(weights)
        {
            m_assignment.resize(m_soft.size(), false);
        }
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
                wth = alloc(smt::theory_weighted_maxsat, m, s);
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
            lbool is_sat = l_true;
            {
                solver::scoped_push _s(s);
                bool was_sat = false;
                for (unsigned i = 0; i < m_soft.size(); ++i) {
                    wth.assert_weighted(m_soft[i].get(), m_weights[i]);
                }
                while (l_true == is_sat) {
                    is_sat = s.check_sat_core(0,0);
                    if (is_sat == l_true) {
                        if (wth.is_optimal()) {
                            s.get_model(m_model);
                        }
                        expr_ref fml = wth.mk_block();
                        s.assert_expr(fml);
                        was_sat = true;
                    }
                }
                if (was_sat) {
                    wth.get_assignment(m_assignment);
                }
                if (is_sat == l_false && was_sat) {
                    is_sat = l_true;
                }
            }
            m_upper = wth.get_min_cost();
            if (is_sat == l_true) {
                m_lower = m_upper;
            }
            TRACE("opt", tout << "min cost: " << m_upper << "\n";);
            wth.reset();
            return is_sat;            
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
    bool wmaxsmt::get_assignment(unsigned idx) const {
        return m_imp->m_assignment[idx];
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

