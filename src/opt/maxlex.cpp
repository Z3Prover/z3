/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    maxlex.cpp

Abstract:
   
    MaxLex solves weighted max-sat problems where weights impose lexicographic order.
    MaxSAT is particularly easy for this class:
     In order of highest weight, check if soft constraint can be satisfied.
     If so, assert it, otherwise assert the negation and record whether the soft 
     constraint is true or false in the solution.

Author:

    Nikolaj Bjorner (nbjorner) 2019-25-1

--*/

#include "opt/opt_context.h"
#include "opt/maxsmt.h"
#include "opt/maxlex.h"

namespace opt {

    bool is_maxlex(weights_t & _ws) {
        vector<rational> ws(_ws);
        std::sort(ws.begin(), ws.end());
        ws.reverse();
        rational sum(0);
        for (rational const& w : ws) {
            sum += w;
        }
        for (rational const& w : ws) {
            if (sum > w + w) return false;
            sum -= w;
        }
        return true;
    }

    class maxlex : public maxsmt_solver_base {

        struct cmp_soft {
            bool operator()(soft const& s1, soft const& s2) const {
                return s1.weight > s2.weight;
            }
        };

        ast_manager&    m;
        maxsat_context& m_c;
        
        void update_assignment() {
            model_ref mdl;
            s().get_model(mdl);
            if (mdl) {
                m_model = mdl;
                m_c.model_updated(mdl.get());
                update_assignment(mdl);
            }
        }

        void assert_value(soft& soft) {
            switch (soft.value) {
            case l_true:
                s().assert_expr(soft.s);
                break;
            case l_false: 
                s().assert_expr(expr_ref(m.mk_not(soft.s), m));
                break;
            default:
                break;
            }
        }

        void set_value(soft& soft, lbool v) {
            soft.set_value(v);
            assert_value(soft);
        }

        void update_assignment(model_ref & mdl) {
            bool first_undef = true, second_undef = false;
            for (auto & soft : m_soft) {
                if (first_undef && soft.value != l_undef) {
                    continue;
                }
                first_undef = false;
                if (soft.value != l_false) {
                    lbool v = mdl->is_true(soft.s) ? l_true : l_undef;;
                    if (v == l_undef) {
                        second_undef = true;
                    }
                    if (second_undef) {
                        soft.set_value(v);
                    }
                    else {
                        set_value(soft, v); // also update constraints
                    }
                }
            }
            update_bounds();
        }
        
        void update_bounds() {
            m_lower.reset();
            m_upper.reset();
            for (auto & soft : m_soft) {
                switch (soft.value) {
                case l_undef:
                    m_upper += soft.weight;
                    break;
                case l_true:
                    break;
                case l_false:
                    m_lower += soft.weight;
                    m_upper += soft.weight;
                    break;
                }
            }
            trace_bounds("maxlex");
        }

        void init() {
            for (auto & soft : m_soft) {
                soft.set_value(l_undef);
            }
            model_ref mdl;
            s().get_model(mdl);
            if (mdl) update_assignment(mdl);           
        }

        lbool maxlex1() {
            for (auto & soft : m_soft) {
                if (soft.value == l_true) {
                    continue;
                }
                SASSERT(soft.value == l_undef);
                expr* a = soft.s;                
                lbool is_sat = s().check_sat(1, &a);
                switch (is_sat) {
                case l_false: 
                    set_value(soft, l_false);
                    update_bounds();
                    break;
                case l_true:
                    update_assignment();
                    SASSERT(soft.value == l_true);
                    break;
                case l_undef:
                    return l_undef;
                }
            }
            return l_true;
        }

        // try two literals per round.
        // doesn't seem to make a difference based on sample test.
        lbool maxlex2() {
            unsigned sz = m_soft.size();
            for (unsigned i = 0; i < sz; ++i) {
                auto& soft = m_soft[i];
                if (soft.value != l_undef) {
                    continue;
                }
                SASSERT(soft.value == l_undef);
                if (i + 1 == sz) {
                    expr* a = soft.s;                
                    lbool is_sat = s().check_sat(1, &a);
                    switch (is_sat) {
                    case l_false: 
                        set_value(soft, l_false);
                        update_bounds();
                        break;
                    case l_true:
                        update_assignment();
                        SASSERT(soft.value == l_true);
                        break;
                    case l_undef:
                        return l_undef;
                    }
                }                
                else {
                    auto& soft2 = m_soft[i+1];
                    expr_ref_vector core(m);
                    expr* a = soft.s;
                    expr* b = soft2.s;
                    expr* asms[2] = { a, b };
                    lbool is_sat = s().check_sat(2, asms);
                    switch (is_sat) {
                    case l_true:
                        update_assignment();
                        SASSERT(soft.value == l_true);
                        SASSERT(soft2.value == l_true);
                        break;
                    case l_false:
                        s().get_unsat_core(core);
                        if (core.contains(b)) {
                            expr_ref not_b(mk_not(m, b), m);
                            asms[1] = not_b;
                            switch (s().check_sat(2, asms)) {
                            case l_true:
                                // a, b is unsat, a, not b is sat.
                                set_value(soft2, l_false);
                                update_assignment();
                                SASSERT(soft.value == l_true);
                                SASSERT(soft2.value == l_false);
                                break;
                            case l_false:
                                // a, b is unsat, a, not b is unsat -> a is unsat
                                // b is unsat, a, not b is unsat -> not a, not b
                                set_value(soft, l_false);
                                // core1 = { b }
                                // core2 = { a, not b }
                                if (!core.contains(a)) {
                                    set_value(soft2, l_false);
                                }
                                else {
                                    // core1 = { a, b}
                                    // core2 = { not_b }
                                    core.reset();
                                    s().get_unsat_core(core);
                                    if (!core.contains(a)) {
                                        set_value(soft2, l_true);
                                    }
                                }
                                update_bounds();
                                break;
                            case l_undef:
                                return l_undef;
                            }
                        }
                        else {
                            set_value(soft, l_false);
                            update_bounds();
                        }
                        break;
                    case l_undef:
                        return l_undef;
                    }
                }
            }
            return l_true;
        }

        // every time probing whether to include soft_i, 
        // include suffix that is known to be assignable to T
        lbool maxlexN() {
            unsigned sz = m_soft.size();
            for (unsigned i = 0; i < sz; ++i) {
                auto& soft = m_soft[i];
                if (soft.value != l_undef) {
                    continue;
                }
                expr_ref_vector asms(m);
                asms.push_back(soft.s);
                for (unsigned j = i + 1; j < sz; ++j) {
                    auto& soft2 = m_soft[j];
                    if (soft2.value == l_true) {
                        asms.push_back(soft2.s);                    
                    }
                }
                lbool is_sat = s().check_sat(asms);
                switch (is_sat) {
                case l_true:
                    update_assignment();
                    SASSERT(soft.value == l_true);
                    break;
                case l_false:
                    set_value(soft, l_false);
                    for (unsigned j = i + 1; j < sz; ++j) {
                        auto& soft2 = m_soft[j];
                        if (soft2.value != l_true) {
                            break;
                        }                        
                        assert_value(soft2);
                    }
                    update_bounds();
                    break;
                case l_undef:
                    return l_undef;
                }
            }
            return l_true;
        }

    public:

        maxlex(maxsat_context& c, unsigned id, weights_t & ws, expr_ref_vector const& s):
            maxsmt_solver_base(c, ws, s),
            m(c.get_manager()),
            m_c(c) {
            // ensure that soft constraints are sorted with largest soft constraints first.
            cmp_soft cmp;
            std::sort(m_soft.begin(), m_soft.end(), cmp);
        }            
        
        lbool operator()() override {
            init();            
            return maxlexN();
        }


        void commit_assignment() override {
            for (auto & soft : m_soft) {
                if (soft.value == l_undef) {
                    return;
                }
                assert_value(soft);
            }
        }
    };

    maxsmt_solver_base* mk_maxlex(maxsat_context& c, unsigned id, weights_t & ws, expr_ref_vector const& soft) {
        return alloc(maxlex, c, id, ws, soft);
    }

}
