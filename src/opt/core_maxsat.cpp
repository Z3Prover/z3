/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    core_maxsat.h

Abstract:

    Core and SAT guided MaxSAT with cardinality constraints.

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-9

Notes:

--*/
#include "core_maxsat.h"
#include "pb_decl_plugin.h"
#include "ast_pp.h"

namespace opt {

        
    core_maxsat::core_maxsat(ast_manager& m, solver& s, expr_ref_vector& soft_constraints):
        m(m), s(s), m_soft(soft_constraints), m_answer(m) {
        m_upper = m_soft.size();
    }
    
    core_maxsat::~core_maxsat() {}
    
    lbool core_maxsat::operator()() {
        expr_ref_vector aux(m);         // auxiliary variables to track soft constraints
        expr_set core_vars;             // variables used so far in some core
        expr_set block_vars;            // variables that should be blocked.
        solver::scoped_push _sp(s);
        for (unsigned i = 0; i < m_soft.size(); ++i) {
            expr* a = m.mk_fresh_const("p", m.mk_bool_sort());
            aux.push_back(m.mk_not(a));
            s.assert_expr(m.mk_or(a, m_soft[i].get()));
            block_vars.insert(aux.back());
        }            
        while (m_answer.size() < m_upper) {
            ptr_vector<expr> vars;
            set2vector(block_vars, vars);
            lbool is_sat = s.check_sat(vars.size(), vars.c_ptr());
            
            switch(is_sat) {
            case l_undef: 
                return l_undef;
            case l_true: {
                model_ref model;
                expr_ref_vector ans(m);
                s.get_model(model);
                
                for (unsigned i = 0; i < aux.size(); ++i) {
                    expr_ref val(m);
                    VERIFY(model->eval(m_soft[i].get(), val));
                    if (m.is_true(val)) {
                        ans.push_back(m_soft[i].get());
                    }
                }
                TRACE("opt", tout << "sat\n";
                      for (unsigned i = 0; i < ans.size(); ++i) {
                          tout << mk_pp(ans[i].get(), m) << "\n";
                      });
                IF_VERBOSE(1, verbose_stream() << "(maxsat.core sat with lower bound: " << ans.size() << "\n";);
                if (ans.size() > m_answer.size()) {
                    m_answer.reset();
                    m_answer.append(ans);
                }
                if (m_answer.size() == m_upper) {
                    return l_true;
                }
                SASSERT(m_soft.size() >= m_answer.size()+1);
                unsigned k = m_soft.size()-m_answer.size()-1;
                expr_ref fml = mk_at_most(core_vars, k);
                TRACE("opt", tout << "add: " << fml << "\n";);
                s.assert_expr(fml);
                break;                    
            }
            case l_false: {
                ptr_vector<expr> core;
                s.get_unsat_core(core);
                TRACE("opt", tout << "core";
                      for (unsigned i = 0; i < core.size(); ++i) {
                          tout << mk_pp(core[i], m) << " ";
                      }
                      tout << "\n";);
                for (unsigned i = 0; i < core.size(); ++i) {
                    core_vars.insert(get_not(core[i]));
                    block_vars.remove(core[i]);
                }
                IF_VERBOSE(1, verbose_stream() << "(maxsat.core unsat (core size = " << core.size() << ")\n";);
                if (core.empty()) {
                    m_upper = m_answer.size();
                    return l_true;
                }
                else {
                    // at least one core variable is True
                    expr_ref fml = mk_at_most(core_vars, 0);
                    fml = m.mk_not(fml);
                    TRACE("opt", tout << "add: " << fml << "\n";);
                    s.assert_expr(fml);
                }
                --m_upper;                
            }
            }            
        }
        return l_true;
    }
    
    void core_maxsat::set2vector(expr_set const& set, ptr_vector<expr>& es) const {
        es.reset();
        expr_set::iterator it = set.begin(), end = set.end();
        for (; it != end; ++it) {
            es.push_back(*it);
        }
    }

    expr_ref core_maxsat::mk_at_most(expr_set const& set, unsigned k) {
        pb_util pb(m);
        ptr_vector<expr> es;
        set2vector(set, es);
        return expr_ref(pb.mk_at_most_k(es.size(), es.c_ptr(), k), m);
    }

    expr* core_maxsat::get_not(expr* e) const {
        expr* result = 0;
        VERIFY(m.is_not(e, result));
        return result;
    }
    
    rational core_maxsat::get_lower() const {
        return rational(m_answer.size());
    }
    rational core_maxsat::get_upper() const {
        return rational(m_upper);
    }
    rational core_maxsat::get_value() const {
        return get_lower();
    }
    expr_ref_vector core_maxsat::get_assignment() const {
        return m_answer;
    }
    void core_maxsat::set_cancel(bool f) {
        
    }
    
};
