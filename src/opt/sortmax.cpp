/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    sortmax.cpp

Abstract:

    Theory based MaxSAT.

Author:

    Nikolaj Bjorner (nbjorner) 2016-11-18

Notes:

--*/
#include "maxsmt.h"
#include "uint_set.h"
#include "ast_pp.h"
#include "model_smt2_pp.h"
#include "smt_theory.h"
#include "smt_context.h"
#include "opt_context.h"
#include "sorting_network.h"
#include "filter_model_converter.h"

namespace opt {

    class sortmax : public maxsmt_solver_base {
    public:
        typedef expr* literal;
        typedef ptr_vector<expr> literal_vector;
        psort_nw<sortmax> m_sort;
        expr_ref_vector   m_trail;
        func_decl_ref_vector m_fresh;
        ref<filter_model_converter> m_filter;
        sortmax(maxsat_context& c, weights_t& ws, expr_ref_vector const& soft): 
            maxsmt_solver_base(c, ws, soft), m_sort(*this), m_trail(m), m_fresh(m) {}

        virtual ~sortmax() {}

        lbool operator()() {
            obj_map<expr, rational> soft;            
            if (!init()) {
                return l_false;
            }
            lbool is_sat = find_mutexes(soft);
            if (is_sat != l_true) {
                return is_sat;
            }
            m_filter = alloc(filter_model_converter, m);
            rational offset = m_lower;
            m_upper = offset;
            expr_ref_vector in(m);
            expr_ref tmp(m);
            ptr_vector<expr> out;
            obj_map<expr, rational>::iterator it = soft.begin(), end = soft.end();
            for (; it != end; ++it) {
                if (!it->m_value.is_unsigned()) {
                    throw default_exception("sortmax can only handle unsigned weights. Use a different heuristic.");
                }
                unsigned n = it->m_value.get_unsigned();
                while (n > 0) {
                    in.push_back(it->m_key);
                    --n;
                }
            }
            m_sort.sorting(in.size(), in.c_ptr(), out);

            // initialize sorting network outputs using the initial assignment.
            unsigned first = 0;
            it = soft.begin();
            for (; it != end; ++it) {
                expr_ref tmp(m);
                if (m_model->eval(it->m_key, tmp) && m.is_true(tmp)) {
                    unsigned n = it->m_value.get_unsigned();
                    while (n > 0) {
                        s().assert_expr(out[first]);
                        ++first;
                        --n;
                    }
                }
                else {
                    m_upper += it->m_value;
                }
            }
            while (l_true == is_sat && first < out.size() && m_lower < m_upper) {
                trace_bounds("sortmax");
                s().assert_expr(out[first]);
                is_sat = s().check_sat(0, 0);
                TRACE("opt", tout << is_sat << "\n"; s().display(tout); tout << "\n";);
                if (m.canceled()) {
                    is_sat = l_undef;
                }
                if (is_sat == l_true) {
                    ++first;
                    s().get_model(m_model);
                    update_assignment();
                    for (; first < out.size() && is_true(out[first]); ++first) { 
                        s().assert_expr(out[first]);
                    }
                    TRACE("opt", model_smt2_pp(tout, m, *m_model.get(), 0););
                    m_upper = m_lower + rational(out.size() - first);
                    (*m_filter)(m_model);
                }
            }
            if (is_sat == l_false) {
                is_sat = l_true;
                m_lower = m_upper;
            }
            TRACE("opt", tout << "min cost: " << m_upper << "\n";);
            return is_sat;
        }

        void update_assignment() {
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                m_assignment[i] = is_true(m_soft[i]);
            }
        }

        bool is_true(expr* e) {
            expr_ref tmp(m);
            return m_model->eval(e, tmp) && m.is_true(tmp);
        }

        // definitions used for sorting network
        literal mk_false() { return m.mk_false(); }
        literal mk_true() { return m.mk_true(); }
        literal mk_max(literal a, literal b) { return trail(m.mk_or(a, b)); }
        literal mk_min(literal a, literal b) { return trail(m.mk_and(a, b)); }
        literal mk_not(literal a) { if (m.is_not(a,a)) return a; return trail(m.mk_not(a)); }

        std::ostream& pp(std::ostream& out, literal lit) {  return out << mk_pp(lit, m);  }
        
        literal trail(literal l) {
            m_trail.push_back(l);
            return l;
        }
        literal fresh() {
            expr_ref fr(m.mk_fresh_const("sn", m.mk_bool_sort()), m);
            func_decl* f = to_app(fr)->get_decl();
            m_fresh.push_back(f);
            m_filter->insert(f);
            return trail(fr);
        }
        
        void mk_clause(unsigned n, literal const* lits) {
            s().assert_expr(mk_or(m, n, lits));
        }        
        
    };
    
    
    maxsmt_solver_base* mk_sortmax(maxsat_context& c, weights_t& ws, expr_ref_vector const& soft) {
        return alloc(sortmax, c, ws, soft);
    }

}
