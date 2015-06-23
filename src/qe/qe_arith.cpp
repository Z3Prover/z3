/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    qe_arith.cpp

Abstract:

    Simple projection function for real arithmetic based on Loos-W.

Author:

    Nikolaj Bjorner (nbjorner) 2013-09-12

Revision History:


--*/

#include "qe_arith.h"
#include "qe_util.h"
#include "ast_util.h"
#include "arith_decl_plugin.h"
#include "ast_pp.h"
#include "th_rewriter.h"
#include "expr_functors.h"

namespace qe {
    
    class arith_project_util {
        ast_manager& m;
        arith_util   a;
        th_rewriter  m_rw;
        expr_ref_vector  m_ineq_terms;
        vector<rational> m_ineq_coeffs;
        svector<bool>    m_ineq_strict;
        scoped_ptr<contains_app> m_var;

        struct cant_project {};

        void is_linear(rational const& mul, expr* t, rational& c, expr_ref_vector& ts) {
            expr* t1, *t2;
            rational mul1;
            if (t == m_var->x()) {
                c += mul;
            }
            else if (a.is_mul(t, t1, t2) && a.is_numeral(t1, mul1)) {
                is_linear(mul* mul1, t2, c, ts);
            }
            else if (a.is_mul(t, t1, t2) && a.is_numeral(t2, mul1)) {
                is_linear(mul* mul1, t1, c, ts);
            }
            else if (a.is_add(t)) {
                app* ap = to_app(t);
                for (unsigned i = 0; i < ap->get_num_args(); ++i) {
                    is_linear(mul, ap->get_arg(i), c, ts);
                }
            }
            else if (a.is_sub(t, t1, t2)) {
                is_linear(mul,  t1, c, ts);
                is_linear(-mul, t2, c, ts);
            }
            else if (a.is_uminus(t, t1)) {
                is_linear(-mul, t1, c, ts);
            }
            else if (a.is_numeral(t, mul1)) {
                ts.push_back(a.mk_numeral(mul*mul1, m.get_sort(t)));
            }
            else if ((*m_var)(t)) {
                IF_VERBOSE(1, verbose_stream() << "can't project:" << mk_pp(t, m) << "\n";);
                throw cant_project();
            }
            else if (mul.is_one()) {
                ts.push_back(t);
            }
            else {
                ts.push_back(a.mk_mul(a.mk_numeral(mul, m.get_sort(t)), t));
            }
        }

        bool is_linear(expr* lit, rational& c, expr_ref& t, bool& is_strict) {
            if (!(*m_var)(lit)) {
                return false;
            }
            expr* e1, *e2;
            c.reset();
            sort* s;
            expr_ref_vector ts(m);            
            bool is_not = m.is_not(lit, lit);
            rational mul(1);
            if (is_not) {
                mul.neg();
            }
            SASSERT(!m.is_not(lit));
            if (a.is_le(lit, e1, e2) || a.is_ge(lit, e2, e1)) {
                is_linear( mul, e1, c, ts);
                is_linear(-mul, e2, c, ts);
                s = m.get_sort(e1);
                is_strict = is_not;
            }
            else if (a.is_lt(lit, e1, e2) || a.is_gt(lit, e2, e1)) {
                is_linear( mul, e1, c, ts);
                is_linear(-mul, e2, c, ts);
                s = m.get_sort(e1);
                is_strict = !is_not;
            }
            else if (m.is_eq(lit, e1, e2) && !is_not) {
                is_linear( mul, e1, c, ts);
                is_linear(-mul, e2, c, ts);
                s = m.get_sort(e1);
                is_strict = false;
            }            
            else {
                IF_VERBOSE(1, verbose_stream() << "can't project:" << mk_pp(lit, m) << "\n";);
                throw cant_project();
            }
            if (ts.empty()) {
                t = a.mk_numeral(rational(0), s);
            }
            else {
                t = a.mk_add(ts.size(), ts.c_ptr());
            }
            return true;
        }

        void project(model& model, expr_ref_vector& lits) {
            unsigned num_pos = 0;
            unsigned num_neg = 0;
            m_ineq_terms.reset();
            m_ineq_coeffs.reset();
            m_ineq_strict.reset();
            expr_ref_vector new_lits(m);
            for (unsigned i = 0; i < lits.size(); ++i) {
                rational c(0);
                expr_ref t(m);
                bool is_strict;
                if (is_linear(lits[i].get(), c, t, is_strict)) {
                    m_ineq_coeffs.push_back(c);
                    m_ineq_terms.push_back(t);
                    m_ineq_strict.push_back(is_strict);
                    if (c.is_zero()) {
                        m_rw(lits[i].get(), t);
                        new_lits.push_back(t);
                    }
                    else if (c.is_pos()) {
                        ++num_pos;
                    }
                    else {
                        ++num_neg;
                    }                    
                }
                else {
                    new_lits.push_back(lits[i].get());
                }
            }
            lits.reset();
            lits.append(new_lits);
            if (num_pos == 0 || num_neg == 0) {
                return;
            }
            bool use_pos = num_pos < num_neg;
            unsigned max_t = find_max(model, use_pos);

            for (unsigned i = 0; i < m_ineq_terms.size(); ++i) {
                if (i != max_t) {
                    if (m_ineq_coeffs[i].is_pos() == use_pos) {
                        lits.push_back(mk_le(i, max_t));
                    }
                    else {
                        lits.push_back(mk_lt(i, max_t));
                    }
                }
            }
        }

        unsigned find_max(model& mdl, bool do_pos) {
            unsigned result;
            bool found = false;
            rational found_val(0), r, found_c;
            expr_ref val(m);
            for (unsigned i = 0; i < m_ineq_terms.size(); ++i) {
                rational const& ac = m_ineq_coeffs[i];
                if (ac.is_pos() == do_pos) {
                    VERIFY(mdl.eval(m_ineq_terms[i].get(), val));
                    VERIFY(a.is_numeral(val, r));
                    r /= abs(ac);
                    IF_VERBOSE(1, verbose_stream() << "max: " << mk_pp(m_ineq_terms[i].get(), m) << " " << r << " " << (!found || r > found_val) << "\n";);
                    if (!found || r > found_val) {
                        result = i;
                        found_val = r;
                        found_c = ac;
                        found = true;
                    }
                }
            }
            SASSERT(found);
            if (a.is_int(m_var->x()) && !found_c.is_one()) {
                throw cant_project();
            }
            return result;
        }

        // ax + t <= 0
        // bx + s <= 0
        // a and b have different signs.
        // Infer: a|b|x + |b|t + |a|bx + |a|s <= 0
        // e.g.   |b|t + |a|s <= 0
        expr_ref mk_lt(unsigned i, unsigned j) {
            rational const& ac = m_ineq_coeffs[i];
            rational const& bc = m_ineq_coeffs[j];
            SASSERT(ac.is_pos() != bc.is_pos());
            SASSERT(ac.is_neg() != bc.is_neg());
            expr* t = m_ineq_terms[i].get();
            expr* s = m_ineq_terms[j].get();
            expr_ref bt = mk_mul(abs(bc), t);
            expr_ref as = mk_mul(abs(ac), s);
            expr_ref ts = mk_add(bt, as);
            expr*    z  = a.mk_numeral(rational(0), m.get_sort(t));
            expr_ref result1(m), result2(m);
            if (m_ineq_strict[i] || m_ineq_strict[j]) {
                result1 = a.mk_lt(ts, z);
            }
            else {
                result1 = a.mk_le(ts, z);
            }
            m_rw(result1, result2);
            return result2;
        }

        // ax + t <= 0
        // bx + s <= 0
        // a and b have same signs.
        // encode:// t/|a| <= s/|b|
        // e.g.   |b|t <= |a|s
        expr_ref mk_le(unsigned i, unsigned j) {
            rational const& ac = m_ineq_coeffs[i];
            rational const& bc = m_ineq_coeffs[j];
            SASSERT(ac.is_pos() == bc.is_pos());
            SASSERT(ac.is_neg() == bc.is_neg());
            expr* t = m_ineq_terms[i].get();
            expr* s = m_ineq_terms[j].get();
            expr_ref bt = mk_mul(abs(bc), t);
            expr_ref as = mk_mul(abs(ac), s);
            expr_ref result1(m), result2(m);
            if (m_ineq_strict[j] && !m_ineq_strict[i]) {
                result1 = a.mk_lt(bt, as);
            }
            else {
                result1 = a.mk_le(bt, as);
            }
            m_rw(result1, result2);
            return result2;
        }


        expr_ref mk_add(expr* t1, expr* t2) {
            return expr_ref(a.mk_add(t1, t2), m);
        }
        expr_ref mk_mul(rational const& r, expr* t2) {
            expr* t1 = a.mk_numeral(r, m.get_sort(t2));
            return expr_ref(a.mk_mul(t1, t2), m);
        }

    public:
        arith_project_util(ast_manager& m): 
            m(m), a(m), m_rw(m), m_ineq_terms(m) {}

        expr_ref operator()(model& model, app_ref_vector& vars, expr_ref_vector const& lits) {
            app_ref_vector new_vars(m);
            expr_ref_vector result(lits);
            for (unsigned i = 0; i < vars.size(); ++i) {
                app* v = vars[i].get();
                m_var = alloc(contains_app, m, v);
                try {
                    project(model, result);
                    TRACE("qe", tout << "projected: " << mk_pp(v, m) << " ";
                          for (unsigned i = 0; i < result.size(); ++i) {
                              tout << mk_pp(result[i].get(), m) << "\n";
                          });
                }
                catch (cant_project) {
                    IF_VERBOSE(1, verbose_stream() << "can't project:" << mk_pp(v, m) << "\n";);
                    new_vars.push_back(v);
                }
            }
            vars.reset();
            vars.append(new_vars);
            return qe::mk_and(result);
        }  
    };

    expr_ref arith_project(model& model, app_ref_vector& vars, expr_ref_vector const& lits) {
        ast_manager& m = vars.get_manager();
        arith_project_util ap(m);
        return ap(model, vars, lits);
    }

    expr_ref arith_project(model& model, app_ref_vector& vars, expr* fml) {
        ast_manager& m = vars.get_manager();
        arith_project_util ap(m);
        expr_ref_vector lits(m);
        flatten_and(fml, lits);
        return ap(model, vars, lits);
    }

}
