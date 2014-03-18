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
#include "opt_params.hpp"
#include "pb_decl_plugin.h"
#include "uint_set.h"
#include "pb_preprocess_tactic.h"
#include "simplify_tactic.h"
#include "tactical.h"
#include "tactic.h"
#include "model_smt2_pp.h"

namespace smt {

    class theory_weighted_maxsat : public theory {
        struct stats {
            unsigned m_num_blocks;
            void reset() { memset(this, 0, sizeof(*this)); }
            stats() { reset(); }
        };
        
        opt::opt_solver&            s;
        mutable unsynch_mpz_manager m_mpz;
        app_ref_vector           m_vars;        // Auxiliary variables per soft clause
        expr_ref_vector          m_fmls;        // Formulas per soft clause
        app_ref                  m_min_cost_atom; // atom tracking modified lower bound
        app_ref_vector           m_min_cost_atoms;
        bool_var                 m_min_cost_bv; // max cost Boolean variable
        vector<rational>         m_rweights;    // weights of theory variables.
        scoped_mpz_vector        m_zweights;
        scoped_mpz_vector        m_old_values;
        svector<theory_var>      m_costs;       // set of asserted theory variables
        svector<theory_var>      m_cost_save;   // set of asserted theory variables
        rational                 m_rcost;       // current sum of asserted costs
        rational                 m_rmin_cost;   // current maximal cost assignment.
        scoped_mpz               m_zcost;       // current sum of asserted costs
        scoped_mpz               m_zmin_cost;   // current maximal cost assignment.
        u_map<theory_var>        m_bool2var;    // bool_var -> theory_var
        svector<bool_var>        m_var2bool;    // theory_var -> bool_var
        bool                     m_propagate;  
        bool                     m_normalize; 
        rational                 m_den;         // lcm of denominators for rational weights.
        svector<bool>            m_assigned;
        stats                    m_stats;

    public:
        theory_weighted_maxsat(ast_manager& m, opt::opt_solver& s):
            theory(m.mk_family_id("weighted_maxsat")),
            s(s),
            m_vars(m),
            m_fmls(m),
            m_min_cost_atom(m),
            m_min_cost_atoms(m),
            m_zweights(m_mpz),
            m_old_values(m_mpz),
            m_zcost(m_mpz),
            m_zmin_cost(m_mpz),
            m_propagate(false),
            m_normalize(false)
        {}

        virtual ~theory_weighted_maxsat() { }

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
                  tout << "\nassignment: ";
                  for (unsigned i = 0; i < result.size(); ++i) {
                      tout << result[i] << " ";
                  }
                  tout << "\n";);                  

        }

        virtual void init_search_eh() {
            m_propagate = true;
        }

        void assert_weighted(expr* fml, rational const& w) {
            context & ctx = get_context();
            ast_manager& m = get_manager();
            app_ref var(m), wfml(m);
            var = m.mk_fresh_const("w", m.mk_bool_sort());
            s.mc().insert(var->get_decl());
            wfml = m.mk_or(var, fml);
            ctx.assert_expr(wfml);
            m_rweights.push_back(w);
            m_vars.push_back(var);
            m_fmls.push_back(fml);
            m_assigned.push_back(false);
            m_rmin_cost += w;
            m_normalize = true;
            register_var(var, true);
        }

        bool_var register_var(app* var, bool attach) {
            context & ctx = get_context();
            ast_manager& m = get_manager();
            bool_var bv;
            SASSERT(!ctx.e_internalized(var));
            enode* x = ctx.mk_enode(var, false, true, true);
            if (ctx.b_internalized(var)) {
                bv = ctx.get_bool_var(var);
            }
            else {
                bv = ctx.mk_bool_var(var);
            }
            ctx.set_enode_flag(bv, true);
            if (attach) {
                ctx.set_var_theory(bv, get_id());                    
                theory_var v = mk_var(x);
                ctx.attach_th_var(x, this, v);
                m_bool2var.insert(bv, v);
                SASSERT(v == m_var2bool.size());
                m_var2bool.push_back(bv);
                SASSERT(ctx.bool_var2enode(bv));
            }
            return bv;
        }

        rational const& get_min_cost() { 
            unsynch_mpq_manager mgr;
            scoped_mpq q(mgr);
            mgr.set(q, m_zmin_cost, m_den.to_mpq().numerator());
            m_rmin_cost = rational(q);
            return m_rmin_cost; 
        }

        expr* set_min_cost(rational const& c) { 
            m_normalize = true;
            ast_manager& m = get_manager();
            std::ostringstream strm;
            strm << "cost <= " << c;
            m_rmin_cost = c; 
            m_min_cost_atom = m.mk_fresh_const(strm.str().c_str(), m.mk_bool_sort());
            m_min_cost_atoms.push_back(m_min_cost_atom);
            s.mc().insert(m_min_cost_atom->get_decl());

            m_min_cost_bv = register_var(m_min_cost_atom, false);

            return m_min_cost_atom;
        }

        bool found_solution() const {
            return !m_cost_save.empty();
        }

        // scoped_mpz leaks.

        class numeral_trail : public trail<context> {
            typedef scoped_mpz T;
            T & m_value;
            scoped_mpz_vector&  m_old_values;

            // numeral_trail(numeral_trail const& nt);
            
        public:
            numeral_trail(T & value, scoped_mpz_vector& old):
                m_value(value),
                m_old_values(old) {
                old.push_back(value);
            }
            
            virtual ~numeral_trail() {
            }
            
            virtual void undo(context & ctx) {
                m_value = m_old_values.back();
                m_old_values.pop_back();
            }
        };

        virtual void assign_eh(bool_var v, bool is_true) {
            TRACE("opt", tout << "Assign " << mk_pp(m_vars[m_bool2var[v]].get(), get_manager()) << " " << is_true << "\n";);
            if (is_true) {
                if (m_normalize) normalize();
                context& ctx = get_context();
                theory_var tv = m_bool2var[v];
                if (m_assigned[tv]) return;
                mpz const& w = m_zweights[tv];
                ctx.push_trail(numeral_trail(m_zcost, m_old_values));
                ctx.push_trail(push_back_vector<context, svector<theory_var> >(m_costs));
                ctx.push_trail(value_trail<context, bool>(m_assigned[tv]));
                m_zcost += w;
                m_costs.push_back(tv);
                m_assigned[tv] = true;
                if (m_zcost > m_zmin_cost) {
                    block();
                }
            }
        }

        virtual final_check_status final_check_eh() {
            if (m_normalize) normalize();
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
            m_rweights.reset();
            m_costs.reset();
            m_rmin_cost.reset();
            m_rcost.reset();
            m_zweights.reset();
            m_zcost.reset();
            m_zmin_cost.reset();
            m_cost_save.reset();
            m_bool2var.reset();
            m_var2bool.reset();
            m_min_cost_atom = 0;
            m_min_cost_atoms.reset();
            m_propagate = false;
            m_assigned.reset();
        }

        virtual theory * mk_fresh(context * new_ctx) { return 0; }
        virtual bool internalize_atom(app * atom, bool gate_ctx) { return false; }
        virtual bool internalize_term(app * term) { return false; }
        virtual void new_eq_eh(theory_var v1, theory_var v2) { }
        virtual void new_diseq_eh(theory_var v1, theory_var v2) { }

        virtual void collect_statistics(::statistics & st) const {
            st.update("wmaxsat num blocks", m_stats.m_num_blocks);
        }

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
            return m_mpz.lt(m_zcost, m_zmin_cost);
        }

        expr_ref mk_block() {
            ++m_stats.m_num_blocks;
            ast_manager& m = get_manager();
            expr_ref_vector disj(m);
            compare_cost compare_cost(*this);
            svector<theory_var> costs(m_costs);
            std::sort(costs.begin(), costs.end(), compare_cost);
            scoped_mpz weight(m_mpz);
            m_mpz.reset(weight);
            for (unsigned i = 0; i < costs.size() && m_mpz.lt(weight, m_zmin_cost); ++i) {
                weight += m_zweights[costs[i]];
                disj.push_back(m.mk_not(m_vars[costs[i]].get()));
            }
            if (m_min_cost_atom) {
                disj.push_back(m.mk_not(m_min_cost_atom));
            }
            if (is_optimal()) {
                unsynch_mpq_manager mgr;
                scoped_mpq q(mgr);
                mgr.set(q, m_zmin_cost, m_den.to_mpq().numerator());
                rational rw = rational(q);
                IF_VERBOSE(1, verbose_stream() << "(wmaxsat with upper bound: " << rw << ")\n";);
                m_zmin_cost = weight;
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
            ++m_stats.m_num_blocks;
            ast_manager& m = get_manager();
            context& ctx = get_context();
            literal_vector lits;
            compare_cost compare_cost(*this);
            svector<theory_var> costs(m_costs);
            std::sort(costs.begin(), costs.end(), compare_cost);
            
            scoped_mpz weight(m_mpz);
            m_mpz.reset(weight);
            for (unsigned i = 0; i < costs.size() && weight < m_zmin_cost; ++i) {
                weight += m_zweights[costs[i]];
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


        void normalize() {
            m_den = rational::one();
            for (unsigned i = 0; i < m_rweights.size(); ++i) {
                m_den = lcm(m_den, denominator(m_rweights[i]));
            }
            m_den = lcm(m_den, denominator(m_rmin_cost));
            SASSERT(!m_den.is_zero());
            m_zweights.reset();
            for (unsigned i = 0; i < m_rweights.size(); ++i) {
                rational r = m_rweights[i]*m_den;
                SASSERT(r.is_int());
                mpq const& q = r.to_mpq();
                m_zweights.push_back(q.numerator());
            }
            rational r = m_rcost* m_den;
            m_zcost = r.to_mpq().numerator();
            r = m_rmin_cost * m_den;
            m_zmin_cost = r.to_mpq().numerator();
            m_normalize = false;
        }
       
        class compare_cost {
            theory_weighted_maxsat& m_th;
        public:
            compare_cost(theory_weighted_maxsat& t):m_th(t) {}
            bool operator() (theory_var v, theory_var w) const { 
                return m_th.m_mpz.gt(m_th.m_zweights[v], m_th.m_zweights[w]); 
            }
        };
    };

}

namespace opt {

    struct wmaxsmt::imp {
        ast_manager&     m;
        opt_solver&      s;
        expr_ref_vector  m_soft;
        svector<bool>    m_assignment;
        vector<rational> m_weights;
        rational         m_upper;
        rational         m_lower;
        model_ref        m_model;
        symbol           m_engine;
        bool             m_print_all_models;
        volatile bool    m_cancel;
        params_ref       m_params;
        opt_solver       m_solver;
        scoped_ptr<imp>  m_imp;

        imp(ast_manager& m, opt_solver& s, expr_ref_vector const& soft_constraints, vector<rational> const& weights):
            m(m), s(s), m_soft(soft_constraints), m_weights(weights), m_print_all_models(false), m_cancel(false), 
            m_solver(m, m_params, symbol("bound"))
        {
            m_assignment.resize(m_soft.size(), false);
        }

        ~imp() {}

        void re_init(expr_ref_vector const& soft, vector<rational> const& weights) {
            m_soft.reset();
            m_soft.append(soft);
            m_weights.reset();
            m_weights.append(weights);
            m_assignment.reset();
            m_assignment.resize(m_soft.size(), false);
            m_lower.reset();
            m_upper.reset();
        }

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

        smt::theory_weighted_maxsat* ensure_theory() {
            smt::theory_weighted_maxsat* wth = get_theory();
            if (wth) {
                wth->reset();
            }
            else {
                wth = alloc(smt::theory_weighted_maxsat, m, s);
                s.get_context().register_plugin(wth);
            }
            return wth;
        }

        /**
           Takes solver with hard constraints added.
           Returns a maximal satisfying subset of weighted soft_constraints
           that are still consistent with the solver state.
        */
        
        lbool operator()() {
            if (m_engine == symbol("iwmax")) {
                return iterative_solve();
            }
            if (m_engine == symbol("pwmax")) {
                return pb_solve();
            }
            if (m_engine == symbol("wpm2")) {
                return wpm2_solve();
            }
            if (m_engine == symbol("wpm2b")) {
                return wpm2b_solve();
            }
            return incremental_solve();
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

        class scoped_ensure_theory {
            smt::theory_weighted_maxsat* m_wth;
        public:
            scoped_ensure_theory(imp& i) {
                m_wth = i.ensure_theory();
            }
            ~scoped_ensure_theory() {
                m_wth->reset();
            }
            smt::theory_weighted_maxsat& operator()() { return *m_wth; }
        };

        lbool incremental_solve() {
            IF_VERBOSE(3, verbose_stream() << "(incremental solve)\n";);
            TRACE("opt", tout << "weighted maxsat\n";);
            scoped_ensure_theory wth(*this);
            solver::scoped_push _s(s);
            lbool is_sat = l_true;
            bool was_sat = false;
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                wth().assert_weighted(m_soft[i].get(), m_weights[i]);
            }
            solver::scoped_push __s(s);
            while (l_true == is_sat) {
                is_sat = s.check_sat_core(0,0);
                if (m_cancel) {
                    is_sat = l_undef;
                }
                if (is_sat == l_true) {
                    if (wth().is_optimal()) {
                        m_upper = wth().get_min_cost();
                        updt_model(s);
                    }
                    expr_ref fml = wth().mk_block();
                    s.assert_expr(fml);
                    was_sat = true;
                }
                IF_VERBOSE(3, verbose_stream() << "(incremental bound)\n";);
            }
            if (was_sat) {
                wth().get_assignment(m_assignment);
            }
            if (is_sat == l_false && was_sat) {
                is_sat = l_true;
            }
            m_upper = wth().get_min_cost();
            if (is_sat == l_true) {
                m_lower = m_upper;
            }
            TRACE("opt", tout << "min cost: " << m_upper << "\n";);
            return is_sat;
        }

        /**
           Iteratively increase cost until there is an assignment during
           final_check that satisfies min_cost.
           
           Takes: log (n / log(n)) iterations
        */
        
        lbool iterative_solve() {
            scoped_ensure_theory wth(*this);
            solver::scoped_push _s(s);
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                wth().assert_weighted(m_soft[i].get(), m_weights[i]);
            }
            solver::scoped_push __s(s);
            rational cost = wth().get_min_cost();
            rational log_cost(1), tmp(1);
            while (tmp < cost) {
                ++log_cost;
                tmp *= rational(2);
            }
            expr_ref_vector bounds(m);
            expr_ref bound(m);
            lbool result = l_false;
            unsigned nsc = 0;
            m_upper = cost;
            while (result == l_false) {
                bound = wth().set_min_cost(log_cost);
                s.push_core();
                ++nsc;
                IF_VERBOSE(1, verbose_stream() << "(wmaxsat.iwmax min cost: " << log_cost << ")\n";);
                TRACE("opt", tout << "cost: " << log_cost << " " << bound << "\n";);
                bounds.push_back(bound);
                result = conditional_solve(bound);
                if (result == l_false) {
                    m_lower = log_cost;        
                }
                if (log_cost > cost) {
                    break;
                }
                log_cost *= rational(2);
                if (m_cancel) {
                    result = l_undef;
                }
            }
            s.pop_core(nsc);
            return result;
        }

        lbool conditional_solve(expr* cond) {
            IF_VERBOSE(3, verbose_stream() << "(conditional solve)\n";);
            smt::theory_weighted_maxsat& wth = *get_theory();
            bool was_sat = false;
            lbool is_sat = l_true;
            while (l_true == is_sat) {
                is_sat = s.check_sat_core(1,&cond);
                if (m_cancel) {
                    is_sat = l_undef;
                }
                if (is_sat == l_true) {
                    if (wth.is_optimal()) {
                        s.get_model(m_model);
                        was_sat = true;
                    }
                    expr_ref fml = wth.mk_block();
                    s.assert_expr(fml);
                }
            }
            if (was_sat) {
                wth.get_assignment(m_assignment);
            }
            if (is_sat == l_false && was_sat) {
                is_sat = l_true;
            }
            if (is_sat == l_true) {
                m_lower = m_upper = wth.get_min_cost();
            }
            TRACE("opt", tout << "min cost: " << m_upper << "\n";);
            return is_sat;            
        }


        // convert bounds constraint into pseudo-Boolean

        lbool pb_solve() {
            pb_util u(m);
            expr_ref fml(m), val(m);
            app_ref b(m);
            expr_ref_vector nsoft(m);
            m_lower = m_upper = rational::zero();
            solver::scoped_push __s(s);
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                m_upper += m_weights[i];
                b = m.mk_fresh_const("b", m.mk_bool_sort());
                s.mc().insert(b->get_decl());
                fml = m.mk_or(m_soft[i].get(), b);
                s.assert_expr(fml);
                nsoft.push_back(b);
            }
            lbool is_sat = l_true;
            bool was_sat = false;
            while (l_true == is_sat) {
                is_sat = s.check_sat_core(0,0);
                if (m_cancel) {
                    is_sat = l_undef;
                }
                if (is_sat == l_true) {
                    s.get_model(m_model);
                    m_upper = rational::zero();
                    for (unsigned i = 0; i < m_soft.size(); ++i) {
                        VERIFY(m_model->eval(nsoft[i].get(), val));
                        m_assignment[i] = !m.is_true(val);
                        if (!m_assignment[i]) {
                            m_upper += m_weights[i];
                        }
                    }                    
                    IF_VERBOSE(1, verbose_stream() << "(wmaxsat.pb with upper bound: " << m_upper << " )\n";);
                    fml = m.mk_not(u.mk_ge(nsoft.size(), m_weights.c_ptr(), nsoft.c_ptr(), m_upper));
                    s.assert_expr(fml);
                    was_sat = true;
                }
            }            
            if (is_sat == l_false && was_sat) {
                is_sat = l_true;
                m_lower = m_upper;
            }
            return is_sat;
        }

        expr* mk_not(expr* e) {
            if (m.is_not(e, e)) {
                return e;
            }
            else {
                return m.mk_not(e);
            }
        }

        lbool pb_simplify_solve() {
            TRACE("opt", s.display(tout); tout << "\n";
                  for (unsigned i = 0; i < m_soft.size(); ++i) {
                      tout << mk_pp(m_soft[i].get(), m) << " " << m_weights[i] << "\n";
                  }
                  );
            pb_util u(m);
            expr_ref fml(m), val(m);
            expr_ref_vector nsoft(m);
            m_lower = m_upper = rational::zero();
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                m_upper += m_weights[i];
                nsoft.push_back(mk_not(m_soft[i].get()));
            }
            solver::scoped_push _s1(s);
            lbool is_sat = l_true;
            bool was_sat = false;
            fml = m.mk_true();
            while (l_true == is_sat) {
                TRACE("opt", s.display(tout<<"looping\n"););
                solver::scoped_push _s2(s);
                s.assert_expr(fml);
                is_sat = simplify_and_check_sat(0,0);
                if (m_cancel) {
                    is_sat = l_undef;
                }
                if (is_sat == l_true) {
                    m_upper = rational::zero();
                    for (unsigned i = 0; i < m_soft.size(); ++i) {
                        VERIFY(m_model->eval(m_soft[i].get(), val));
                        TRACE("opt", tout << "eval " << mk_pp(m_soft[i].get(), m) << " " << val << "\n";);
                        m_assignment[i] = m.is_true(val);
                        if (!m_assignment[i]) {
                            m_upper += m_weights[i];
                        }
                    }                     
                    TRACE("opt", tout << "new upper: " << m_upper << "\n";);
                    IF_VERBOSE(1, verbose_stream() << "(wmaxsat.pb solve with upper bound: " << m_upper << ")\n";);
                    fml = m.mk_not(u.mk_ge(nsoft.size(), m_weights.c_ptr(), nsoft.c_ptr(), m_upper));
                    was_sat = true;
                }
            }            
            if (is_sat == l_false && was_sat) {
                is_sat = l_true;
                m_lower = m_upper;
            }
            TRACE("opt", tout << "lower: " << m_lower << "\n";);
            return is_sat;
        }


        lbool wpm2_solve() {
            solver::scoped_push _s(s);
            pb_util u(m);
            app_ref fml(m), a(m), b(m), c(m);
            expr_ref val(m);
            expr_ref_vector block(m), ans(m), al(m), am(m);
            m_lower = m_upper = rational::zero();
            obj_map<expr, unsigned> ans_index;

            vector<rational> amk;
            vector<uint_set> sc;
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                rational w = m_weights[i];
                m_upper += w;

                b = m.mk_fresh_const("b", m.mk_bool_sort());
                s.mc().insert(b->get_decl());
                block.push_back(b);
                expr* bb = b;

                a = m.mk_fresh_const("a", m.mk_bool_sort());
                s.mc().insert(a->get_decl());
                ans.push_back(a);
                ans_index.insert(a, i);
                fml = m.mk_or(m_soft[i].get(), b, m.mk_not(a));
                s.assert_expr(fml);
                
                c = m.mk_fresh_const("c", m.mk_bool_sort());
                s.mc().insert(c->get_decl());
                fml = m.mk_implies(c, u.mk_le(1,&w,&bb,rational(0)));
                s.assert_expr(fml);

                sc.push_back(uint_set());
                sc.back().insert(i);                
                am.push_back(c);
                amk.push_back(rational(0));
            }

            while (true) {
                expr_ref_vector asms(m);
                ptr_vector<expr> core;
                asms.append(ans);
                asms.append(am);
                lbool is_sat = s.check_sat(asms.size(), asms.c_ptr());
                TRACE("opt", 
                      tout << "\nassumptions: ";
                      for (unsigned i = 0; i < asms.size(); ++i) {
                          tout << mk_pp(asms[i].get(), m) << " ";
                      }
                      tout << "\n" << is_sat << "\n";
                      tout << "upper: " << m_upper << "\n";
                      tout << "lower: " << m_lower << "\n";
                      if (is_sat == l_true) {
                          model_ref mdl;
                          s.get_model(mdl);
                          model_smt2_pp(tout, m, *(mdl.get()), 0);
                      });

                if (m_cancel && is_sat != l_false) {
                    is_sat = l_undef;
                }
                if (is_sat == l_true) {
                    m_upper = m_lower;
                    updt_model(s);
                    for (unsigned i = 0; i < block.size(); ++i) {
                        VERIFY(m_model->eval(m_soft[i].get(), val));
                        TRACE("opt", tout << mk_pp(block[i].get(), m) << " " << val << "\n";);
                        m_assignment[i] = m.is_true(val);
                    }
                }
                if (is_sat != l_false) {
                    return is_sat;
                }
                s.get_unsat_core(core);
                if (core.empty()) {
                    return l_false;
                }
                TRACE("opt",
                      tout << "core: ";
                      for (unsigned i = 0; i < core.size(); ++i) {
                          tout << mk_pp(core[i],m) << " ";
                      }
                      tout << "\n";);
                uint_set A;
                for (unsigned i = 0; i < core.size(); ++i) {
                    unsigned j;
                    if (ans_index.find(core[i], j)) {
                        A.insert(j);
                    }
                }
                if (A.empty()) {
                    return l_false;
                }
                uint_set B;
                rational k(0);
                rational old_lower(m_lower);
                for (unsigned i = 0; i < sc.size(); ++i) {
                    uint_set t(sc[i]);
                    t &= A;
                    if (!t.empty()) {
                        B |= sc[i];
                        k += amk[i];
                        m_lower -= amk[i];
                        sc[i] = sc.back();
                        sc.pop_back();
                        am[i] = am.back();
                        am.pop_back();
                        amk[i] = amk.back();
                        amk.pop_back();
                        --i;
                    }
                }
                vector<rational> ws;
                expr_ref_vector  bs(m);
                for (unsigned i = 0; i < m_soft.size(); ++i) {
                    if (B.contains(i)) {
                        ws.push_back(m_weights[i]);
                        bs.push_back(block[i].get());
                    }
                }
                TRACE("opt", tout << "at most bound: " << k << "\n";);
                is_sat = new_bound(al, ws, bs, k);
                if (is_sat != l_true) {
                    return is_sat;
                }
                m_lower += k;
                SASSERT(m_lower > old_lower);
                TRACE("opt", tout << "new bound: " << m_lower << "\n";);
                expr_ref B_le_k(m), B_ge_k(m);
                B_le_k = u.mk_le(ws.size(), ws.c_ptr(), bs.c_ptr(), k);
                B_ge_k = u.mk_ge(ws.size(), ws.c_ptr(), bs.c_ptr(), k);
                s.assert_expr(B_ge_k);
                al.push_back(B_ge_k);
                IF_VERBOSE(1, verbose_stream() << "(wmaxsat.wpm2 lower bound: " << m_lower << ")\n";);
                IF_VERBOSE(2, verbose_stream() << "New lower bound: " << B_ge_k << "\n";);

                c = m.mk_fresh_const("c", m.mk_bool_sort());
                s.mc().insert(c->get_decl());
                fml = m.mk_implies(c, B_le_k);
                s.assert_expr(fml);
                sc.push_back(B);
                am.push_back(c);
                amk.push_back(k);
            }            
        }
        
        // Version from CP'13        
        lbool wpm2b_solve() {
            solver::scoped_push _s(s);
            pb_util u(m);
            app_ref fml(m), a(m), b(m), c(m);
            expr_ref val(m);
            expr_ref_vector block(m), ans(m), am(m), soft(m);
            m_lower = m_upper = rational::zero();
            obj_map<expr, unsigned> ans_index;

            vector<rational> amk;
            vector<uint_set> sc;    // vector of indices used in at last constraints
            expr_ref_vector  al(m); // vector of at least constraints.
            rational wmax;
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                rational w = m_weights[i];
                m_upper += w;
                if (wmax < w) wmax = w;
                b = m.mk_fresh_const("b", m.mk_bool_sort());
                block.push_back(b);
                expr* bb = b;
                s.mc().insert(b->get_decl());
                a = m.mk_fresh_const("a", m.mk_bool_sort());
                s.mc().insert(a->get_decl());
                ans.push_back(a);
                ans_index.insert(a, i);
                soft.push_back(0); // assert soft constraints lazily.
                
                c = m.mk_fresh_const("c", m.mk_bool_sort());
                s.mc().insert(c->get_decl());
                fml = m.mk_implies(c, u.mk_le(1,&w,&bb,rational(0)));
                s.assert_expr(fml);

                sc.push_back(uint_set());
                sc.back().insert(i);                
                am.push_back(c);

                al.push_back(u.mk_ge(1,&w,&bb,rational(0)));
                s.assert_expr(al.back());

                amk.push_back(rational(0));
            }
            ++wmax;

            while (true) {
                enable_soft(soft, block, ans, wmax);
                expr_ref_vector asms(m);
                asms.append(ans);
                asms.append(am);
                lbool is_sat = s.check_sat(asms.size(), asms.c_ptr());
                if (m_cancel && is_sat != l_false) {
                    is_sat = l_undef;
                }
                if (is_sat == l_undef) {
                    return l_undef;
                }
                if (is_sat == l_true && wmax.is_zero()) {
                    m_upper = m_lower;
                    updt_model(s);
                    for (unsigned i = 0; i < block.size(); ++i) {
                        VERIFY(m_model->eval(block[i].get(), val));
                        m_assignment[i] = m.is_false(val);
                    }
                    return l_true;
                }
                if (is_sat == l_true) {
                    rational W(0);
                    for (unsigned i = 0; i < m_weights.size(); ++i) {
                        if (m_weights[i] < wmax) W += m_weights[i];
                    }
                    harden(am, W);
                    wmax = decrease(wmax);
                    continue;
                }
                SASSERT(is_sat == l_false);
                ptr_vector<expr> core;
                s.get_unsat_core(core);
                if (core.empty()) {
                    return l_false;
                }
                uint_set A;
                for (unsigned i = 0; i < core.size(); ++i) {
                    unsigned j;
                    if (ans_index.find(core[i], j) && soft[j].get()) {
                        A.insert(j);
                    }
                }
                if (A.empty()) {
                    return l_false;
                }
                uint_set B;
                rational k;
                for (unsigned i = 0; i < sc.size(); ++i) {
                    uint_set t(sc[i]);
                    t &= A;
                    if (!t.empty()) {
                        B |= sc[i];
                        m_lower -= amk[i];
                        k += amk[i];
                        sc[i] = sc.back();
                        sc.pop_back();
                        am[i] = am.back();
                        am.pop_back();
                        amk[i] = amk.back();
                        amk.pop_back();
                        --i;
                    }
                }
                vector<rational> ws;
                expr_ref_vector  bs(m);
                for (unsigned i = 0; i < m_soft.size(); ++i) {
                    if (B.contains(i)) {
                        ws.push_back(m_weights[i]);
                        bs.push_back(block[i].get());
                    }
                }

                expr_ref_vector al2(al);
                for (unsigned i = 0; i < s.get_num_assertions(); ++i) {
                    al2.push_back(s.get_assertion(i));
                }
                is_sat = new_bound(al2, ws, bs, k);
                if (is_sat != l_true) {
                    return is_sat;
                }
                m_lower += k;
                expr_ref B_le_k(m), B_ge_k(m);
                B_le_k = u.mk_le(ws.size(), ws.c_ptr(), bs.c_ptr(), k);
                B_ge_k = u.mk_ge(ws.size(), ws.c_ptr(), bs.c_ptr(), k);
                s.assert_expr(B_ge_k);
                al.push_back(B_ge_k);
                IF_VERBOSE(1, verbose_stream() << "(wmaxsat.wpm2 lower bound: " << m_lower << ")\n";);
                IF_VERBOSE(2, verbose_stream() << "New lower bound: " << B_ge_k << "\n";);

                c = m.mk_fresh_const("c", m.mk_bool_sort());
                s.mc().insert(c->get_decl());
                fml = m.mk_implies(c, B_le_k);
                s.assert_expr(fml);
                sc.push_back(B);
                am.push_back(c);
                amk.push_back(k);
            }            
        }

        void harden(expr_ref_vector& am, rational const& W) {
            // TBD 
        }
        
        rational decrease(rational const& wmax) {
            rational wmin(0);
            for (unsigned i = 0; i < m_weights.size(); ++i) {
                rational w = m_weights[i];
                if (w < wmax && wmin < w) wmin = w;
            }
            return wmin;
        }
   

        // enable soft constraints that have reached wmax.
        void enable_soft(expr_ref_vector& soft, 
                         expr_ref_vector const& block, 
                         expr_ref_vector const& ans, 
                         rational wmax) {
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                rational w = m_weights[i];
                if (w >= wmax && !soft[i].get()) {
                    soft[i] = m.mk_or(m_soft[i].get(), block[i], m.mk_not(ans[i]));
                    s.assert_expr(soft[i].get());
                }           
            }     
        }                               

        lbool new_bound(expr_ref_vector const& al, 
                        vector<rational> const& ws, 
                        expr_ref_vector const& bs, 
                        rational& k) {
            pb_util u(m);
            expr_ref_vector al2(m);
            al2.append(al);
            // w_j*b_j > k
            al2.push_back(m.mk_not(u.mk_le(ws.size(), ws.c_ptr(), bs.c_ptr(), k)));            
            return bound(al2, ws, bs, k);
        }

        // 
        // minimal k, such that  al & w_j*b_j >= k is sat
        // minimal k, such that  al & 3*x + 4*y >= k is sat
        // minimal k, such that al & (or (not x) w3) & (or (not y) w4)
        //
        lbool bound(expr_ref_vector const& al, 
                    vector<rational> const& ws, 
                    expr_ref_vector const& bs,
                    rational& k) {
            expr_ref_vector nbs(m);
            opt_solver::scoped_push _sc(m_solver);
            for (unsigned i = 0; i < al.size(); ++i) {
                m_solver.assert_expr(al[i]);
            }
            for (unsigned i = 0; i < bs.size(); ++i) {
                nbs.push_back(mk_not(bs[i]));
            }    
            TRACE("opt", 
                  m_solver.display(tout);
                  tout << "\n";
                  for (unsigned i = 0; i < bs.size(); ++i) {
                      tout << mk_pp(bs[i], m) << " " << ws[i] << "\n";
                  });
            m_imp->re_init(nbs, ws); 
            lbool is_sat = m_imp->pb_simplify_solve();
            SASSERT(m_imp->m_lower > k);
            k = m_imp->m_lower;
            return is_sat;
        }

        void updt_params(params_ref& p) {
            opt_params _p(p);
            m_engine = _p.wmaxsat_engine();        
            m_print_all_models = _p.print_all_models();
            m_solver.updt_params(p);
            if (m_imp) {
                m_imp->updt_params(p);
            }
        }

        void updt_model(solver& s) {
            s.get_model(m_model);
            if (m_print_all_models) {
                std::cout << "[" << m_lower << ":" << m_upper << "]\n";
                std::cout << "(model " << std::endl;
                model_smt2_pp(std::cout, m, *(m_model.get()), 2);
                std::cout << ")" << std::endl;                 
            }
        }

        lbool simplify_and_check_sat(unsigned n, expr* const* assumptions) {
            lbool is_sat = l_true;
            tactic_ref tac1 = mk_simplify_tactic(m);
            // tactic_ref tac2 = mk_pb_preprocess_tactic(m); 
            tactic_ref tac  = tac1; // and_then(tac1.get(), tac2.get());  // TBD: make attribute for cancelation.
            proof_converter_ref pc;
            expr_dependency_ref core(m);
            model_converter_ref mc;
            goal_ref_buffer result;
            goal_ref g(alloc(goal, m, true, false));
            for (unsigned i = 0; i < s.get_num_assertions(); ++i) {
                g->assert_expr(s.get_assertion(i));
            }
            for (unsigned i = 0; i < n; ++i) {
                NOT_IMPLEMENTED_YET();
                // add assumption in a wrapper.
            }
            (*tac)(g, result, mc, pc, core);
            if (result.empty()) {
                is_sat = l_false;
            }
            else {
                SASSERT(result.size() == 1);
                goal_ref r = result[0];
                solver::scoped_push _s(m_solver);
                // TBD ptr_vector<expr> asms;
                for (unsigned i = 0; i < r->size(); ++i) {
                    // TBD collect assumptions from r
                    m_solver.assert_expr(r->form(i));
                }
                is_sat = m_solver.check_sat_core(0, 0);
                if (l_true == is_sat && !m_cancel) {
                    updt_model(m_solver);
                    if (mc && m_model) (*mc)(m_model, 0);
                    IF_VERBOSE(2, 
                               g->display(verbose_stream() << "goal:\n");
                               r->display(verbose_stream() << "reduced:\n");
                               model_smt2_pp(verbose_stream(), m, *m_model, 0););
                }
            }
            return is_sat;
        }

    };

    wmaxsmt::wmaxsmt(ast_manager& m, opt_solver& s, expr_ref_vector& soft_constraints, vector<rational> const& weights) {
        m_imp = alloc(imp, m, s, soft_constraints, weights);
        m_imp->m_imp = alloc(imp, m, m_imp->m_solver, soft_constraints, weights);
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
        m_imp->m_cancel = f;
        m_imp->m_solver.set_cancel(f);
        m_imp->m_imp->m_cancel = f;        
        m_imp->m_imp->m_solver.set_cancel(f);
    }
    void wmaxsmt::collect_statistics(statistics& st) const {
        m_imp->m_solver.collect_statistics(st);
    }
    void wmaxsmt::get_model(model_ref& mdl) {
        m_imp->get_model(mdl);
    }

    void wmaxsmt::updt_params(params_ref& p) {
        m_imp->updt_params(p);
    }    

};

#if 0
// The case m_lower = 0, m_upper = 1 is not handled correctly.
// cost becomes 0

        lbool bisection_solve() {
            IF_VERBOSE(3, verbose_stream() << "(bisection solve)\n";);
            TRACE("opt", tout << "weighted maxsat\n";);
            scoped_ensure_theory wth(*this);
            solver::scoped_push _s(s);
            lbool is_sat = l_true;
            bool was_sat = false;
            expr_ref_vector bounds(m);
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                wth().assert_weighted(m_soft[i].get(), m_weights[i]);
            }
            solver::scoped_push __s(s);
            m_lower = rational::zero();
            m_upper = wth().get_min_cost();
            while (m_lower < m_upper && is_sat != l_undef) {
                rational cost = div(m_upper + m_lower, rational(2));
                
                bounds.push_back(wth().set_min_cost(cost));
                is_sat = s.check_sat_core(1,bounds.c_ptr()+bounds.size()-1);
                if (m_cancel) {
                    is_sat = l_undef;
                }
                switch(is_sat) {
                case l_true: {
                    if (wth().is_optimal()) {
                        updt_model(s);
                    }
                    expr_ref fml = wth().mk_block();
                    s.assert_expr(fml);
                    m_upper = wth().get_min_cost();
                    IF_VERBOSE(1, verbose_stream() << "(wmaxsat.bwmax max cost: " << m_upper << ")\n";);
                    break;
                }
                case l_false: {
                    m_lower = cost;
                    IF_VERBOSE(1, verbose_stream() << "(wmaxsat.bwmax min cost: " << m_lower << ")\n";);
                    break;
                }
                case l_undef:
                    break;
                }
            }
            if (was_sat) {
                is_sat = l_true;
            }
            return is_sat;
        }
#endif
