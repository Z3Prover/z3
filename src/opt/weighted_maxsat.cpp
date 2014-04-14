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

#include <typeinfo>
#include "weighted_maxsat.h"
#include "smt_theory.h"
#include "smt_context.h"
#include "ast_pp.h"
#include "theory_wmaxsat.h"
#include "opt_params.hpp"
#include "pb_decl_plugin.h"
#include "uint_set.h"
#include "pb_preprocess_tactic.h"
#include "simplify_tactic.h"
#include "tactical.h"
#include "tactic.h"
#include "model_smt2_pp.h"
#include "pb_sls.h"
#include "qfbv_tactic.h"
#include "card2bv_tactic.h"
#include "tactic2solver.h"
#include "bvsls_opt_engine.h"
#include "nnf_tactic.h"

namespace opt {

    struct wmaxsmt::imp {
        ast_manager&     m;
        opt_solver&      s;                  // solver state that contains hard constraints
        expr_ref_vector  m_soft;             // set of soft constraints
        vector<rational> m_weights;          // their weights
        svector<bool>    m_assignment;       // truth assignment to soft constrsaints
        rational         m_upper;            // current upper bound for wmaxsmt
        rational         m_lower;            // current lower bound for wmaxsmt
        model_ref        m_model;            // current best model is stored here.
        symbol           m_engine;           // config
        bool             m_print_all_models; // config
        params_ref       m_params;           // config
        volatile bool    m_cancel;
        opt_solver       m_solver;           // used for recursively calling maxsmt
        scoped_ptr<imp>  m_imp;              // 
        ref<solver>      m_sat_solver;       // used for maxsmt over QF_BV
        smt::pb_sls      m_sls;              // used for sls improvement of assignment
        bvsls_opt_engine m_bvsls;            // used for bvsls improvements of assignment
        

        imp(ast_manager& m, opt_solver& s, expr_ref_vector const& soft_constraints, vector<rational> const& weights):
            m(m), s(s), m_soft(soft_constraints), 
            m_weights(weights), m_print_all_models(false), m_cancel(false), 
            m_solver(m, m_params, symbol("bound")),
            m_sls(m),
            m_bvsls(m, m_params)
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

        smt::theory_wmaxsat* get_theory() const {
            smt::context& ctx = s.get_context();                        
            smt::theory_id th_id = m.get_family_id("weighted_maxsat");
            smt::theory* th = ctx.get_theory(th_id);               
            if (th) {
                return dynamic_cast<smt::theory_wmaxsat*>(th);
            }
            else {
                return 0;
            }
        }

        smt::theory_wmaxsat* ensure_theory() {
            smt::theory_wmaxsat* wth = get_theory();
            if (wth) {
                wth->reset();
            }
            else {
                wth = alloc(smt::theory_wmaxsat, m, s.mc_ref());
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
            if (m_engine == symbol("bvmax")) {
                return pb2sat_solve();
            }
            if (m_engine == symbol("wpm2")) {
                return wpm2_solve();
            }
            if (m_engine == symbol("wpm2b")) {
                return wpm2b_solve();
            }
            if (m_engine == symbol("sls")) {
                return sls_solve();
            }
            if (m_engine == symbol("bvsls")) {
                return bvsls_solve();
            }
            if (m_engine == symbol::null || m_engine == symbol("wmax")) {
                return incremental_solve();
            }
            IF_VERBOSE(0, verbose_stream() << "(unknown engine " << m_engine << " using default 'wmax')\n";);
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

        void set_cancel(bool f) {
            if (m_sat_solver) {
                m_sat_solver->set_cancel(f);
            }
            m_sls.set_cancel(f);
            m_bvsls.set_cancel(f);
            m_cancel = f;
            m_solver.set_cancel(f);
            m_imp->m_cancel = f;        
            m_imp->m_solver.set_cancel(f);
        }

        void collect_statistics(statistics& st) const {
            m_solver.collect_statistics(st);
            if (m_sat_solver) {
                m_sat_solver->collect_statistics(st);
            }
        }


        class scoped_ensure_theory {
            smt::theory_wmaxsat* m_wth;
        public:
            scoped_ensure_theory(imp& i) {
                m_wth = i.ensure_theory();
            }
            ~scoped_ensure_theory() {
                m_wth->reset();
            }
            smt::theory_wmaxsat& operator()() { return *m_wth; }
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

        lbool sls_solve() {
            IF_VERBOSE(1, verbose_stream() << "(sls solve)\n";);
            for (unsigned i = 0; i < s.get_num_assertions(); ++i) {
                m_sls.add(s.get_assertion(i));
            }
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
                m_sls.add(m_soft[i].get(), m_weights[i]);
            }
            lbool is_sat = l_true;
            bool was_sat = false;
            while (l_true == is_sat) {
                is_sat = s.check_sat_core(0,0);
                if (m_cancel) {
                    is_sat = l_undef;
                }
                if (is_sat == l_true) {
                    updt_model(s);
                    m_sls.set_model(m_model);
                    m_upper = rational::zero();
                    if (l_true == m_sls()) {
                        m_sls.get_model(m_model);
                        for (unsigned i = 0; i < m_soft.size(); ++i) {
                            m_assignment[i] = m_sls.soft_holds(i);
                        }
                    }
                    else {
                        for (unsigned i = 0; i < m_soft.size(); ++i) {
                            VERIFY(m_model->eval(nsoft[i].get(), val));
                            m_assignment[i] = !m.is_true(val);
                        }        
                    }            
                    for (unsigned i = 0; i < m_soft.size(); ++i) {
                        if (!m_assignment[i]) {
                            m_upper += m_weights[i];
                        }
                    }
                    IF_VERBOSE(1, verbose_stream() << "(sls.pb with upper bound: " << m_upper << ")\n";);
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

        lbool bvsls_solve() {
            IF_VERBOSE(1, verbose_stream() << "(bvsls solve)\n";);

            bv_util bv(m);
            pb::card_pb_rewriter pb_rewriter(m);
            expr_ref tmp(m), objective(m), zero(m);
            expr_ref_vector es(m);

            goal_ref g(alloc(goal, m, true, false));
            for (unsigned i = 0; i < s.get_num_assertions(); ++i) {
                pb_rewriter(s.get_assertion(i), tmp);
                g->assert_expr(tmp);
            }
            tactic_ref simplify = mk_nnf_tactic(m);
            proof_converter_ref pc;
            expr_dependency_ref core(m);
            goal_ref_buffer result;
            model_converter_ref model_converter;
            (*simplify)(g, result, model_converter, pc, core);
            SASSERT(result.size() == 1);
            goal* r = result[0];
            for (unsigned i = 0; i < r->size(); ++i) {
                m_bvsls.assert_expr(r->form(i));
            }

            m_lower = m_upper = rational::zero();

            for (unsigned i = 0; i < m_soft.size(); ++i) {
                m_upper += m_weights[i];
            }
            rational num = numerator(m_upper);
            rational den = denominator(m_upper);
            rational maxval = num*den;
            unsigned bv_size = maxval.get_num_bits();
            zero = bv.mk_numeral(rational(0), bv_size);
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                pb_rewriter(m_soft[i].get(), tmp);
                es.push_back(m.mk_ite(tmp, bv.mk_numeral(den*m_weights[i], bv_size), zero));
            }
            if (es.empty()) {
                objective = bv.mk_numeral(0, bv_size);
            }
            else {
                objective = es[0].get();
                for (unsigned i = 1; i < es.size(); ++i) {
                    objective = bv.mk_bv_add(objective, es[i].get());
                }
            }
            lbool is_sat = s.check_sat_core(0, 0);
            if (is_sat == l_true) {
                updt_model(s);
                params_ref p;
                p.set_uint("restarts", 20);
                m_bvsls.updt_params(p);
                // TBD: can we set an initial model on m_bvsls?
                // CMW: Yes, see next line.                
                bvsls_opt_engine::optimization_result res = m_bvsls.optimize(objective, m_model, true);
                switch (res.is_sat) {
                case l_true: {
                    unsigned bv_size = 0;
                    m_bvsls.get_model(m_model);
                    VERIFY(bv.is_numeral(res.optimum, m_lower, bv_size));
                    for (unsigned i = 0; i < m_soft.size(); ++i) {
                        expr_ref tmp(m);
                        m_model->eval(m_soft[i].get(), tmp, true);
                        m_assignment[i] = m.is_true(tmp);
                    }
                    break;
                }
                case l_false:
                case l_undef:
                    break;
                }
                return res.is_sat;
            }
            else
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
            IF_VERBOSE(1, verbose_stream() << "(wmaxsat.conditional solve)\n";);
            smt::theory_wmaxsat& wth = *get_theory();
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
            fml = m.mk_true();
            while (l_true == is_sat) {
                solver::scoped_push _s(s);
                s.assert_expr(fml);
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
                    IF_VERBOSE(1, verbose_stream() << "(wmaxsat.pb with upper bound: " << m_upper << ")\n";);
                    fml = m.mk_not(u.mk_ge(nsoft.size(), m_weights.c_ptr(), nsoft.c_ptr(), m_upper));
                    was_sat = true;
                }
            }            
            if (is_sat == l_false && was_sat) {
                is_sat = l_true;
                m_lower = m_upper;
            }
            return is_sat;
        }

        //
        // convert bounds constraint into pseudo-Boolean, 
        // then treat pseudo-Booleans as bit-vectors and
        // sorting circuits.
        //
        lbool pb2sat_solve() {
            IF_VERBOSE(1, verbose_stream() << "(wmaxsat.bv solve)\n";);
            pb_util u(m);
            expr_ref fml(m), val(m);
            app_ref b(m);
            expr_ref_vector nsoft(m);
            m_lower = m_upper = rational::zero();
            tactic_ref pb2bv = mk_card2bv_tactic(m, m_params);
            tactic_ref bv2sat = mk_qfbv_tactic(m, m_params);
            tactic_ref tac = and_then(pb2bv.get(), bv2sat.get());
            m_sat_solver = mk_tactic2solver(m, tac.get(), m_params);
            unsigned sz = s.get_num_assertions();
            for (unsigned i = 0; i < sz; ++i) {
                m_sat_solver->assert_expr(s.get_assertion(i));
            }
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                m_upper += m_weights[i];
                b = m.mk_fresh_const("b", m.mk_bool_sort());
                // TODO: s.mc().insert(b->get_decl());
                fml = m.mk_or(m_soft[i].get(), b);
                m_sat_solver->assert_expr(fml);
                nsoft.push_back(b);
            }
            lbool is_sat = l_true;
            bool was_sat = false;
            fml = m.mk_true();
            while (l_true == is_sat) {
                solver::scoped_push __s(*(m_sat_solver));
                m_sat_solver->assert_expr(fml);
                is_sat = m_sat_solver->check_sat(0,0);
                if (m_cancel) {
                    is_sat = l_undef;
                }
                if (is_sat == l_true) {
                    m_sat_solver->get_model(m_model);
                    m_upper = rational::zero();
                    for (unsigned i = 0; i < m_soft.size(); ++i) {
                        VERIFY(m_model->eval(nsoft[i].get(), val));
                        m_assignment[i] = !m.is_true(val);
                        if (!m_assignment[i]) {
                            m_upper += m_weights[i];
                        }
                    }                    
                    IF_VERBOSE(1, verbose_stream() << "(wmaxsat.bv with upper bound: " << m_upper << ")\n";);
                    fml = m.mk_not(u.mk_ge(nsoft.size(), m_weights.c_ptr(), nsoft.c_ptr(), m_upper));
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

        // ------------------------------------------------------
        // Morgado, Heras, Marques-Silva 2013

        struct wcore {
            unsigned_vector m_R;
            rational        m_lower;
            rational        m_mid;
            rational        m_upper;
        };

        lbool bcd2_solve() {
            return l_undef;
#if 0
            expr_ref fml(m), val(m);
            app_ref r(m);
            vector<wcore> cores;
            obj_map<expr, unsigned> ans2core;     // answer literal to core index
            lbool is_sat = l_undef;
            expr_ref_vector soft(m), rs(m);
            m_lower = m_upper = rational::zero();            
            bool first = true;
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                m_upper += m_weights[i];
                r = m.mk_fresh_const("r", m.mk_bool_sort());
                s.mc().insert(r->get_decl());
                fml = m.mk_or(m_soft[i].get(), r);
                s.assert_expr(fml);
                rs.push_back(r);
                asms.push_back(m.mk_not(r));
            }
            m_upper += rational(1);
            solver::scoped_push _s(s);
            while (m_lower < m_upper) {
                solver::scoped_push _s(s);
                if (m_cancel) {
                    return l_undef;
                }
                for (unsigned i = 0; i < cores.size(); ++i) {
                    assert_core(cores[i]);
                    // need assumptions here as well.
                }
                is_sat = check_sat(asms.size(), asms.c_ptr());
                switch(is_sat) {
                case l_undef: 
                    return l_undef;
                case l_true: {
                    updt_model(s);
                    m_upper.reset();
                    for (unsigned i = 0; i < cores.size(); ++i) {
                        wcore& c_i = cores[i];
                        unsigned_vector const& R = c_i.m_R;
                        c_i.m_upper.reset();
                        for (unsigned j = 0; j < R.size(); ++j) {
                            unsigned r_j = R[j];
                            VERIFY(m_model->eval(m_soft[r_j].get(), val));                            
                            if (m.is_false(val)) {
                                c_i.m_upper += m_weights[r_j];
                            }
                        }
                        c_i.m_mid = div(c_i.m_lower + c_i.m_upper, rational(2));
                        m_upper += c_i.m_upper;
                    }                    
                    first = false;
                    break;
                }
                case l_false: {
                    ptr_vector<expr> core;
                    s.get_unsat_core(core);
                    uint_set subC;
                    unsigned_vector soft;
                    rational delta(0);
                    for (unsigned i = 0; i < core.size(); ++i) {
                        unsigned j;
                        if (ans2core.find(core[i], j)) {
                            subC.insert(j);
                            rational new_delta = rational(1) + cores[j].m_upper - cores[j].m_mid; 
                            SASSERT(new_delta.is_pos());
                            if (delta.is_zero() || delta > new_delta) {
                                delta = new_delta;
                            }
                        }
                        else {
                            soft.push_back(i);
                        }
                    }
                    if (soft.empty() && subC.num_elems() == 1) {
                        SASSERT(core.size() == 1);
                        unsigned s = *subS.begin();
                        wcore& c_s = cores[s];
                        m_lower -= c_s.m_lower;
                        c_s.m_lower = refine(c_s, c_s.m_mid);
                        m_lower += c_s.m_lower;
                    }
                    else {
                        wcore c_s;
                        relax(subC, soft, c_s.m_R);
                        for (unsigned i = 0; i < subC.size(); ++i) {
                            
                        }
                    }
                    break;
                }
                }
            }
            return is_sat;
#endif
        }

        void assert_core(wcore const& core) {
            expr_ref fml(m);
            vector<rational> ws;
            ptr_vector<expr> rs;
            for (unsigned j = 0; j < core.m_R.size(); ++j) {
                unsigned idx = core.m_R[j];
                ws.push_back(m_weights[idx]);
                rs.push_back(m_soft[idx].get());   // TBD: check
            }
            // TBD: fml = pb.mk_le(ws.size(), ws.c_ptr(), rs.c_ptr(), core.m_mid);
            s.assert_expr(fml);
        }

        // ------------------------------------------------------
        // AAAI 2010
        lbool wpm2_solve() {
            IF_VERBOSE(1, verbose_stream() << "(wmaxsat.wpm2 solve)\n";);
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
        
        // ------------------------------------------------------
        // Version from CP'13        
        lbool wpm2b_solve() {
            IF_VERBOSE(1, verbose_stream() << "(wmaxsat.wpm2b solve)\n";);
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
        m_imp->set_cancel(f);
    }
    void wmaxsmt::collect_statistics(statistics& st) const {
        m_imp->collect_statistics(st);
    }
    void wmaxsmt::get_model(model_ref& mdl) {
        m_imp->get_model(mdl);
    }

    void wmaxsmt::updt_params(params_ref& p) {
        m_imp->updt_params(p);
    }    

};

#if 0
    class base_solver {
        opt_solver& s;
    public:
        base_solver(opt_solver& s): s(s) {}
        virutal void assert_soft(expr* e, rational const& w) = 0;
        virtual void get_model(model_ref& m) = 0;
        virtual void block() = 0; 
        virtual lbool check() = 0;
        virtual void get_core(ptr_vector<expr>& core) { UNREACHABLE(); }
    };
#endif
