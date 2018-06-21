/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    wmax.cpp

Abstract:

    Theory based MaxSAT.

Author:

    Nikolaj Bjorner (nbjorner) 2014-4-17

Notes:

--*/
#include "opt/wmax.h"
#include "util/uint_set.h"
#include "ast/ast_pp.h"
#include "model/model_smt2_pp.h"
#include "smt/smt_theory.h"
#include "smt/smt_context.h"
#include "smt/theory_wmaxsat.h"
#include "opt/opt_context.h"

namespace opt {
    // ----------------------------------------------------------
    // weighted max-sat using a custom theory solver for max-sat.
    // NB. it is quite similar to pseudo-Boolean propagation.


    class wmax : public maxsmt_solver_base {
        obj_map<expr, rational>  m_weights;
        obj_map<expr, expr*>     m_keys;
        expr_ref_vector m_trail, m_defs;

        void reset() {
            m_weights.reset();
            m_keys.reset();
            m_trail.reset();
            m_defs.reset();
        }

    public:
        wmax(maxsat_context& c, weights_t& ws, expr_ref_vector const& soft): 
            maxsmt_solver_base(c, ws, soft),
            m_trail(m),
            m_defs(m) {}

        virtual ~wmax() {}

        lbool operator()() {
            TRACE("opt", tout << "weighted maxsat\n";);
            scoped_ensure_theory wth(*this);
            obj_map<expr, rational> soft;            
            reset();
            lbool is_sat = find_mutexes(soft);
            if (is_sat != l_true) {
                return is_sat;
            }
            m_upper = m_lower;
            expr_ref_vector asms(m);
            vector<expr_ref_vector> cores;

            obj_map<expr, rational>::iterator it = soft.begin(), end = soft.end();
            for (; it != end; ++it) {
                assert_weighted(wth(), it->m_key, it->m_value);
                if (!is_true(it->m_key)) {
                    m_upper += it->m_value;
                }
            }
            wth().init_min_cost(m_upper - m_lower);
            trace_bounds("wmax");
            
            TRACE("opt", 
                  s().display(tout); tout << "\n";
                  tout << "lower: " << m_lower << " upper: " << m_upper << "\n";);
            while (!m.canceled() && m_lower < m_upper) {
                //mk_assumptions(asms);
                //is_sat = s().preferred_sat(asms, cores);
                is_sat = s().check_sat(0, nullptr);
                if (m.canceled()) {
                    is_sat = l_undef;
                }
                if (is_sat == l_undef) {
                    break;
                }
                if (is_sat == l_false) {
                    TRACE("opt", tout << "Unsat\n";);
                    break;
                }
                if (is_sat == l_true) {
                    if (wth().is_optimal()) {
                        m_upper = m_lower + wth().get_cost();
                        s().get_model(m_model);
                    }
                    expr_ref fml = wth().mk_block();
                    //DEBUG_CODE(verify_cores(cores););
                    s().assert_expr(fml);
                }
                update_cores(wth(), cores);
                wth().init_min_cost(m_upper - m_lower);
                trace_bounds("wmax");
                SASSERT(m_lower <= m_upper);
            }

            update_assignment();
            
            if (!m.canceled() && is_sat == l_undef && m_lower == m_upper) {
                is_sat = l_true;
            }
            if (is_sat == l_false) {
                is_sat = l_true;
                m_lower = m_upper;
            }
            TRACE("opt", tout << "min cost: " << m_upper << "\n";);
            return is_sat;
        }

        bool is_true(expr* e) {
            return m_model->is_true(e);
        }

        void update_assignment() {
            for (soft& s : m_soft) s.is_true = is_true(s.s);
        }

        struct compare_asm {
            wmax& max;
            compare_asm(wmax& max):max(max) {}
            bool operator()(expr* a, expr* b) const {
                return max.m_weights[a] > max.m_weights[b];
            }
        };

        void mk_assumptions(expr_ref_vector& asms) {
            ptr_vector<expr> _asms;
            obj_map<expr, rational>::iterator it = m_weights.begin(), end = m_weights.end();
            for (; it != end; ++it) {
                _asms.push_back(it->m_key);
            }
            compare_asm comp(*this);
            std::sort(_asms.begin(),_asms.end(), comp); 
            asms.reset();
            for (unsigned i = 0; i < _asms.size(); ++i) {
                asms.push_back(m.mk_not(_asms[i]));
            }
        }

        void verify_cores(vector<expr_ref_vector> const& cores) {
            for (unsigned i = 0; i < cores.size(); ++i) {
                verify_core(cores[i]);
            }
        }

        void verify_core(expr_ref_vector const& core) {
            s().push();
            s().assert_expr(core);
            VERIFY(l_false == s().check_sat(0, nullptr));
            s().pop(1);
        }

        void update_cores(smt::theory_wmaxsat& th, vector<expr_ref_vector> const& cores) {
            obj_hashtable<expr> seen;
            bool updated = false;
            unsigned min_core_size = UINT_MAX;
            for (unsigned i = 0; i < cores.size(); ++i) {
                expr_ref_vector const& core = cores[i];
                if (core.size() <= 20) {
                    s().assert_expr(m.mk_not(mk_and(core)));
                }
                min_core_size = std::min(core.size(), min_core_size);
                if (core.size() >= 11) {
                    continue;
                }
                bool found = false;
                for (unsigned j = 0; !found && j < core.size(); ++j) {
                    found = seen.contains(core[j]);
                }
                if (found) {
                    continue;
                }
                for (unsigned j = 0; j < core.size(); ++j) {
                    seen.insert(core[j]);
                }
                update_core(th, core);
                updated = true;
            }
            // if no core was selected, then take the smallest cores.
            for (unsigned i = 0; !updated && i < cores.size(); ++i) {
                expr_ref_vector const& core = cores[i];
                if (core.size() > min_core_size + 2) {
                    continue;
                }
                bool found = false;
                for (unsigned j = 0; !found && j < core.size(); ++j) {
                    found = seen.contains(core[j]);
                }
                if (found) {
                    continue;
                }
                for (unsigned j = 0; j < core.size(); ++j) {
                    seen.insert(core[j]);
                }
                update_core(th, core);                
            }            
        }


        rational remove_negations(smt::theory_wmaxsat& th, expr_ref_vector const& core, ptr_vector<expr>& keys, vector<rational>& weights) {
            rational min_weight(-1);
            for (unsigned i = 0; i < core.size(); ++i) {
                expr* e = nullptr;
                VERIFY(m.is_not(core[i], e));
                keys.push_back(m_keys[e]);
                rational weight = m_weights[e];
                if (i == 0 || weight < min_weight) {
                    min_weight = weight;
                }
                weights.push_back(weight);
                m_weights.erase(e);
                m_keys.erase(e);
                th.disable_var(e);
            }
            for (unsigned i = 0; i < core.size(); ++i) {
                rational weight = weights[i];
                if (weight > min_weight) {
                    weight -= min_weight;
                    assert_weighted(th, keys[i], weight);
                }
            }
            return min_weight;
        }

        // assert maxres clauses
        // assert new core members with value of current model.
        // update lower bound
        // bounds get re-normalized when solver is invoked.
        // each element of core is negated literal from theory_wmaxsat
        // disable those literals from th

        void update_core(smt::theory_wmaxsat& th, expr_ref_vector const& core) {
            ptr_vector<expr> keys;
            vector<rational> weights;
            rational min_weight = remove_negations(th, core, keys, weights);            
            max_resolve(th, keys, min_weight);            
            m_lower += min_weight;
            // std::cout << core << " " << min_weight << "\n";
        }

        void max_resolve(smt::theory_wmaxsat& th, ptr_vector<expr> const& core, rational const& w) {
            SASSERT(!core.empty());
            expr_ref fml(m), asum(m);
            app_ref cls(m), d(m), dd(m);
            //
            // d_0 := true
            // d_i := b_{i-1} and d_{i-1}    for i = 1...sz-1
            // soft (b_i or !d_i) 
            //   == (b_i or !(!b_{i-1} or d_{i-1}))
            //   == (b_i or b_0 & b_1 & ... & b_{i-1})
            // 
            // Soft constraint is satisfied if previous soft constraint
            // holds or if it is the first soft constraint to fail.
            // 
            // Soundness of this rule can be established using MaxRes
            // 
            for (unsigned i = 1; i < core.size(); ++i) {
                expr* b_i = core[i-1];
                expr* b_i1 = core[i];
                if (i == 1) {
                    d = to_app(b_i);
                }
                else if (i == 2) {
                    d = m.mk_and(b_i, d);
                    m_trail.push_back(d);
                }
                else {
                    dd = mk_fresh_bool("d");
                    fml = m.mk_implies(dd, d);
                    s().assert_expr(fml);
                    m_defs.push_back(fml);
                    fml = m.mk_implies(dd, b_i);
                    s().assert_expr(fml);
                    m_defs.push_back(fml);
                    fml = m.mk_and(d, b_i);
                    update_model(dd, fml);
                    d = dd;
                }
                cls = m.mk_or(b_i1, d);
                m_trail.push_back(cls);
                assert_weighted(th, cls, w);
            }
        }

        expr* assert_weighted(smt::theory_wmaxsat& th, expr* key, rational const& w) {
            expr* c = th.assert_weighted(key, w);
            m_weights.insert(c, w);
            m_keys.insert(c, key);
            m_trail.push_back(c);
            return c;
        }

        void update_model(expr* def, expr* value) {
            if (m_model) {
                m_model->register_decl(to_app(def)->get_decl(), (*m_model)(value));
            }
        }
                
    };

    maxsmt_solver_base* mk_wmax(maxsat_context& c, weights_t& ws, expr_ref_vector const& soft) {
        return alloc(wmax, c, ws, soft);
    }

}
