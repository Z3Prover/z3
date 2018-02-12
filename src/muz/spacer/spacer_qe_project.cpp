/*++
Copyright (c) 2010 Microsoft Corporation and Arie Gurfinkel

Module Name:

    spacer_qe_project.cpp

Abstract:

    Simple projection function for real arithmetic based on Loos-W.
    Projection functions for arrays based on MBP

Author:

    Nikolaj Bjorner (nbjorner) 2013-09-12
    Anvesh Komuravelli
    Arie Gurfinkel

Revision History:


--*/

#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/expr_functors.h"
#include "ast/expr_substitution.h"
#include "ast/ast_util.h"

#include "ast/rewriter/expr_replacer.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/rewriter/th_rewriter.h"

#include "model/model_evaluator.h"
#include "model/model_pp.h"

#include "qe/qe.h"
#include "qe/qe_vartest.h"
#include "qe/qe_lite.h"

#include "muz/spacer/spacer_mev_array.h"
#include "muz/spacer/spacer_qe_project.h"

namespace
{
bool is_partial_eq (app* a);

/**
 * \brief utility class for partial equalities
 *
 * A partial equality (a ==I b), for two arrays a,b and a finite set of indices I holds
 *   iff (Forall i. i \not\in I => a[i] == b[i]); in other words, it is a
 *   restricted form of the extensionality axiom
 *
 * using this class, we denote (a =I b) as f(a,b,i0,i1,...)
 *   where f is an uninterpreted predicate with name PARTIAL_EQ and
 *   I = {i0,i1,...}
 */
class peq {
    ast_manager&        m;
    expr_ref            m_lhs;
    expr_ref            m_rhs;
    unsigned            m_num_indices;
    expr_ref_vector     m_diff_indices;
    func_decl_ref       m_decl;     // the partial equality declaration
    app_ref             m_peq;      // partial equality application
    app_ref             m_eq;       // equivalent std equality using def. of partial eq
    array_util          m_arr_u;

public:
    static const char* PARTIAL_EQ;

    peq (app* p, ast_manager& m);

    peq (expr* lhs, expr* rhs, unsigned num_indices, expr * const * diff_indices, ast_manager& m);

    void lhs (expr_ref& result);

    void rhs (expr_ref& result);

    void get_diff_indices (expr_ref_vector& result);

    void mk_peq (app_ref& result);

    void mk_eq (app_ref_vector& aux_consts, app_ref& result, bool stores_on_rhs = true);
};

const char* peq::PARTIAL_EQ = "partial_eq";

peq::peq (app* p, ast_manager& m):
    m (m),
    m_lhs (p->get_arg (0), m),
    m_rhs (p->get_arg (1), m),
    m_num_indices (p->get_num_args ()-2),
    m_diff_indices (m),
    m_decl (p->get_decl (), m),
    m_peq (p, m),
    m_eq (m),
    m_arr_u (m)
{
    VERIFY (is_partial_eq (p));
    SASSERT (m_arr_u.is_array (m_lhs) &&
             m_arr_u.is_array (m_rhs) &&
             ast_eq_proc() (m.get_sort (m_lhs), m.get_sort (m_rhs)));
    for (unsigned i = 2; i < p->get_num_args (); i++) {
        m_diff_indices.push_back (p->get_arg (i));
    }
}

peq::peq (expr* lhs, expr* rhs, unsigned num_indices, expr * const * diff_indices, ast_manager& m):
    m (m),
    m_lhs (lhs, m),
    m_rhs (rhs, m),
    m_num_indices (num_indices),
    m_diff_indices (m),
    m_decl (m),
    m_peq (m),
    m_eq (m),
    m_arr_u (m)
{
    SASSERT (m_arr_u.is_array (lhs) &&
             m_arr_u.is_array (rhs) &&
             ast_eq_proc() (m.get_sort (lhs), m.get_sort (rhs)));
    ptr_vector<sort> sorts;
    sorts.push_back (m.get_sort (m_lhs));
    sorts.push_back (m.get_sort (m_rhs));
    for (unsigned i = 0; i < num_indices; i++) {
        sorts.push_back (m.get_sort (diff_indices [i]));
        m_diff_indices.push_back (diff_indices [i]);
    }
    m_decl = m.mk_func_decl (symbol (PARTIAL_EQ), sorts.size (), sorts.c_ptr (), m.mk_bool_sort ());
}

void peq::lhs (expr_ref& result) { result = m_lhs; }

void peq::rhs (expr_ref& result) { result = m_rhs; }

void peq::get_diff_indices (expr_ref_vector& result) {
    for (unsigned i = 0; i < m_diff_indices.size (); i++) {
        result.push_back (m_diff_indices.get (i));
    }
}

void peq::mk_peq (app_ref& result) {
    if (!m_peq) {
        ptr_vector<expr> args;
        args.push_back (m_lhs);
        args.push_back (m_rhs);
        for (unsigned i = 0; i < m_num_indices; i++) {
            args.push_back (m_diff_indices.get (i));
        }
        m_peq = m.mk_app (m_decl, args.size (), args.c_ptr ());
    }
    result = m_peq;
}

void peq::mk_eq (app_ref_vector& aux_consts, app_ref& result, bool stores_on_rhs) {
    if (!m_eq) {
        expr_ref lhs (m_lhs, m), rhs (m_rhs, m);
        if (!stores_on_rhs) {
            std::swap (lhs, rhs);
        }
        // lhs = (...(store (store rhs i0 v0) i1 v1)...)
        sort* val_sort = get_array_range (m.get_sort (lhs));
        expr_ref_vector::iterator end = m_diff_indices.end ();
        for (expr_ref_vector::iterator it = m_diff_indices.begin ();
                it != end; it++) {
            app* val = m.mk_fresh_const ("diff", val_sort);
            ptr_vector<expr> store_args;
            store_args.push_back (rhs);
            store_args.push_back (*it);
            store_args.push_back (val);
            rhs = m_arr_u.mk_store (store_args.size (), store_args.c_ptr ());
            aux_consts.push_back (val);
        }
        m_eq = m.mk_eq (lhs, rhs);
    }
    result = m_eq;
}


bool is_partial_eq (app* a) {
    return a->get_decl ()->get_name () == peq::PARTIAL_EQ;
}

}


namespace qe {

    class is_relevant_default : public i_expr_pred {
    public:
        bool operator()(expr* e) override {
            return true;
        }
    };

    class mk_atom_default : public i_nnf_atom {
    public:
        void operator()(expr* e, bool pol, expr_ref& result) override {
            if (pol) result = e;
            else result = result.get_manager().mk_not(e);
        }
    };

    class arith_project_util {
        ast_manager& m;
        arith_util   a;
        th_rewriter  m_rw;
        expr_ref_vector  m_lits;
        expr_ref_vector  m_terms;
        vector<rational> m_coeffs;
        vector<rational> m_divs;
        svector<bool>    m_strict;
        svector<bool>    m_eq;
        scoped_ptr<contains_app> m_var;

        bool is_linear(rational const& mul, expr* t, rational& c, expr_ref_vector& ts) {
            expr* t1, *t2;
            rational mul1;
            bool res = true;
            if (t == m_var->x()) {
                c += mul;
            }
            else if (a.is_mul(t, t1, t2) && a.is_numeral(t1, mul1)) {
                res = is_linear(mul* mul1, t2, c, ts);
            }
            else if (a.is_mul(t, t1, t2) && a.is_numeral(t2, mul1)) {
                res = is_linear(mul* mul1, t1, c, ts);
            }
            else if (a.is_add(t)) {
                app* ap = to_app(t);
                for (unsigned i = 0; res && i < ap->get_num_args(); ++i) {
                    res = is_linear(mul, ap->get_arg(i), c, ts);
                }
            }
            else if (a.is_sub(t, t1, t2)) {
                res = is_linear(mul,  t1, c, ts) && is_linear(-mul, t2, c, ts);
            }
            else if (a.is_uminus(t, t1)) {
                res = is_linear(-mul, t1, c, ts);
            }
            else if (a.is_numeral(t, mul1)) {
                ts.push_back(a.mk_numeral(mul*mul1, m.get_sort(t)));
            }
            else if ((*m_var)(t)) {
                IF_VERBOSE(2, verbose_stream() << "can't project:" << mk_pp(t, m) << "\n";);
                TRACE ("qe", tout << "Failed to project: " << mk_pp (t, m) << "\n";);
                res = false;
            }
            else if (mul.is_one()) {
                ts.push_back(t);
            }
            else {
                ts.push_back(a.mk_mul(a.mk_numeral(mul, m.get_sort(t)), t));
            }
            return res;
        }

        // either an equality (cx + t = 0) or an inequality (cx + t <= 0) or a divisibility literal (d | cx + t)
        bool is_linear(expr* lit, rational& c, expr_ref& t, rational& d, bool& is_strict, bool& is_eq, bool& is_diseq) {
            SASSERT ((*m_var)(lit));
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
                if (!is_linear( mul, e1, c, ts) || !is_linear(-mul, e2, c, ts))
                    return false;
                s = m.get_sort(e1);
                is_strict = is_not;
            }
            else if (a.is_lt(lit, e1, e2) || a.is_gt(lit, e2, e1)) {
                if (!is_linear( mul, e1, c, ts) || !is_linear(-mul, e2, c, ts))
                    return false;
                s = m.get_sort(e1);
                is_strict = !is_not;
            }
            else if (m.is_eq(lit, e1, e2) && a.is_int_real (e1)) {
                expr *t, *num;
                rational num_val, d_val, z;
                bool is_int;
                if (a.is_mod (e1, t, num) && a.is_numeral (num, num_val, is_int) && is_int &&
                        a.is_numeral (e2, z) && z.is_zero ()) {
                    // divsibility constraint: t % num == 0 <=> num | t
                    if (num_val.is_zero ()) {
                        IF_VERBOSE(1, verbose_stream() << "div by zero" << mk_pp(lit, m) << "\n";);
                        return false;
                    }
                    d = num_val;
                    if (!is_linear (mul, t, c, ts)) return false;
                } else if (a.is_mod (e2, t, num) && a.is_numeral (num, num_val, is_int) && is_int &&
                        a.is_numeral (e1, z) && z.is_zero ()) {
                    // divsibility constraint: 0 == t % num <=> num | t
                    if (num_val.is_zero ()) {
                        IF_VERBOSE(1, verbose_stream() << "div by zero" << mk_pp(lit, m) << "\n";);
                        return false;
                    }
                    d = num_val;
                    if (!is_linear (mul, t, c, ts)) return false;
                } else {
                    // equality or disequality
                    if (!is_linear( mul, e1, c, ts) || !is_linear(-mul, e2, c, ts))
                        return false;
                    if (is_not) is_diseq = true;
                    else is_eq = true;
                }
                s = m.get_sort(e1);
            }
            else {
                IF_VERBOSE(2, verbose_stream() << "can't project:" << mk_pp(lit, m) << "\n";);
                TRACE ("qe", tout << "Failed to project: " << mk_pp (lit, m) << "\n";);
                return false;
            }

            if (ts.empty()) {
                t = a.mk_numeral(rational(0), s);
            }
            else if (ts.size () == 1) {
                t = ts.get (0);
            }
            else {
                t = a.mk_add(ts.size(), ts.c_ptr());
            }

            return true;
        }

        bool project(model& mdl, expr_ref_vector& lits) {
            unsigned num_pos = 0;
            unsigned num_neg = 0;
            bool use_eq = false;
            expr_ref_vector new_lits(m);
            expr_ref eq_term (m);

            m_lits.reset ();
            m_terms.reset();
            m_coeffs.reset();
            m_strict.reset();
            m_eq.reset ();

            for (unsigned i = 0; i < lits.size(); ++i) {
                rational c(0), d(0);
                expr_ref t(m);
                bool is_strict = false;
                bool is_eq = false;
                bool is_diseq = false;
                if (!(*m_var)(lits.get (i))) {
                    new_lits.push_back(lits.get (i));
                    continue;
                }
                if (is_linear(lits.get (i), c, t, d, is_strict, is_eq, is_diseq)) {
                    if (c.is_zero()) {
                        m_rw(lits.get (i), t);
                        new_lits.push_back(t);
                    } else if (is_eq) {
                        if (!use_eq) {
                            // c*x + t = 0  <=>  x = -t/c
                            eq_term = mk_mul (-(rational::one ()/c), t);
                            use_eq = true;
                        }
                        m_lits.push_back (lits.get (i));
                        m_coeffs.push_back(c);
                        m_terms.push_back(t);
                        m_strict.push_back(false);
                        m_eq.push_back (true);
                    } else {
                        if (is_diseq) {
                            // c*x + t != 0
                            // find out whether c*x + t < 0, or c*x + t > 0
                            expr_ref cx (m), cxt (m), val (m);
                            rational r;
                            cx = mk_mul (c, m_var->x());
                            cxt = mk_add (cx, t);
                            VERIFY(mdl.eval(cxt, val, true));
                            VERIFY(a.is_numeral(val, r));
                            SASSERT (r > rational::zero () || r < rational::zero ());
                            if (r > rational::zero ()) {
                                c = -c;
                                t = mk_mul (-(rational::one()), t);
                            }
                            is_strict = true;
                        }
                        m_lits.push_back (lits.get (i));
                        m_coeffs.push_back(c);
                        m_terms.push_back(t);
                        m_strict.push_back(is_strict);
                        m_eq.push_back (false);
                        if (c.is_pos()) {
                            ++num_pos;
                        }
                        else {
                            ++num_neg;
                        }
                    }
                }
                else return false;
            }
            if (use_eq) {
                TRACE ("qe",
                        tout << "Using equality term: " << mk_pp (eq_term, m) << "\n";
                      );
                // substitute eq_term for x everywhere
                for (unsigned i = 0; i < m_lits.size(); ++i) {
                    expr_ref cx (m), cxt (m), z (m), result (m);
                    cx = mk_mul (m_coeffs[i], eq_term);
                    cxt = mk_add (cx, m_terms.get(i));
                    z = a.mk_numeral(rational(0), m.get_sort(eq_term));
                    if (m_eq[i]) {
                        // c*x + t = 0
                        result = a.mk_eq (cxt, z);
                    } else if (m_strict[i]) {
                        // c*x + t < 0
                        result = a.mk_lt (cxt, z);
                    } else {
                        // c*x + t <= 0
                        result = a.mk_le (cxt, z);
                    }
                    m_rw (result);
                    new_lits.push_back (result);
                }
            }
            lits.reset();
            lits.append(new_lits);
            if (use_eq || num_pos == 0 || num_neg == 0) {
                return true;
            }
            bool use_pos = num_pos < num_neg;
            unsigned max_t = find_max(mdl, use_pos);

            expr_ref new_lit (m);
            for (unsigned i = 0; i < m_lits.size(); ++i) {
                if (i != max_t) {
                    if (m_coeffs[i].is_pos() == use_pos) {
                        new_lit = mk_le(i, max_t);
                    }
                    else {
                        new_lit = mk_lt(i, max_t);
                    }
                    lits.push_back(new_lit);
                    TRACE ("qe",
                            tout << "Old literal: " << mk_pp (m_lits.get (i), m) << "\n";
                            tout << "New literal: " << mk_pp (new_lit, m) << "\n";
                          );
                }
            }
            return true;
        }

        bool project(model& mdl, app_ref_vector const& lits, expr_map& map, app_ref& div_lit) {
            unsigned num_pos = 0; // number of positive literals true in the model
            unsigned num_neg = 0; // number of negative literals true in the model

            m_lits.reset ();
            m_terms.reset();
            m_coeffs.reset();
            m_divs.reset ();
            m_strict.reset();
            m_eq.reset ();

            expr_ref var_val (m);
            VERIFY (mdl.eval (m_var->x(), var_val, true));

            unsigned eq_idx = lits.size ();
            for (unsigned i = 0; i < lits.size(); ++i) {
                rational c(0), d(0);
                expr_ref t(m);
                bool is_strict = false;
                bool is_eq = false;
                bool is_diseq = false;
                if (!(*m_var)(lits.get (i))) continue;
                if (is_linear(lits.get (i), c, t, d, is_strict, is_eq, is_diseq)) {
                    TRACE ("qe",
                            tout << "Literal: " << mk_pp (lits.get (i), m) << "\n";
                          );

                    if (c.is_zero()) {
                        TRACE ("qe",
                                tout << "independent of variable\n";
                              );
                        continue;
                    }

                    // evaluate c*x + t in the model
                    expr_ref cx (m), cxt (m), val (m);
                    rational r;
                    cx = mk_mul (c, m_var->x());
                    cxt = mk_add (cx, t);
                    VERIFY(mdl.eval(cxt, val, true));
                    VERIFY(a.is_numeral(val, r));

                    if (is_eq) {
                        TRACE ("qe",
                                tout << "equality term\n";
                              );
                        // check if the equality is true in the mdl
                        if (eq_idx == lits.size () && r == rational::zero ()) {
                            eq_idx = m_lits.size ();
                        }
                        m_lits.push_back (lits.get (i));
                        m_coeffs.push_back(c);
                        m_terms.push_back(t);
                        m_strict.push_back(false);
                        m_eq.push_back (true);
                        m_divs.push_back (d);
                    } else {
                        TRACE ("qe",
                                tout << "not an equality term\n";
                              );
                        if (is_diseq) {
                            // c*x + t != 0
                            // find out whether c*x + t < 0, or c*x + t > 0
                            if (r > rational::zero ()) {
                                c = -c;
                                t = mk_mul (-(rational::one()), t);
                                r = -r;
                            }
                            // note: if the disequality is false in the model,
                            // r==0 and we end up choosing c*x + t < 0
                            is_strict = true;
                        }
                        m_lits.push_back (lits.get (i));
                        m_coeffs.push_back(c);
                        m_terms.push_back(t);
                        m_strict.push_back(is_strict);
                        m_eq.push_back (false);
                        m_divs.push_back (d);
                        if (d.is_zero ()) { // not a div term
                            if ((is_strict && r < rational::zero ()) ||
                                    (!is_strict && r <= rational::zero ())) { // literal true in the model
                                if (c.is_pos()) {
                                    ++num_pos;
                                }
                                else {
                                    ++num_neg;
                                }
                            }
                        }
                    }
                    TRACE ("qe",
                            tout << "c: " << c << "\n";
                            tout << "t: " << mk_pp (t, m) << "\n";
                            tout << "d: " << d << "\n";
                          );
                }
                else return false;
            }

            rational lcm_coeffs (1), lcm_divs (1);
            if (a.is_int (m_var->x())) {
                // lcm of (absolute values of) coeffs
                for (unsigned i = 0; i < m_lits.size (); i++) {
                    lcm_coeffs = lcm (lcm_coeffs, abs (m_coeffs[i]));
                }
                // normalize coeffs of x to +/-lcm_coeffs and scale terms and divs appropriately;
                // find lcm of scaled-up divs
                for (unsigned i = 0; i < m_lits.size (); i++) {
                    rational factor (lcm_coeffs / abs(m_coeffs[i]));
                    if (!factor.is_one () && !a.is_zero (m_terms.get (i)))
                      m_terms[i] = a.mk_mul (a.mk_numeral (factor, a.mk_int ()),
                                             m_terms.get (i));
                    m_coeffs[i] = (m_coeffs[i].is_pos () ? lcm_coeffs : -lcm_coeffs);
                    if (!m_divs[i].is_zero ()) {
                        m_divs[i] *= factor;
                        lcm_divs = lcm (lcm_divs, m_divs[i]);
                    }
                    TRACE ("qe",
                            tout << "normalized coeff: " << m_coeffs[i] << "\n";
                            tout << "normalized term: " << mk_pp (m_terms.get (i), m) << "\n";
                            tout << "normalized div: " << m_divs[i] << "\n";
                          );
                }

                // consider new divisibility literal (lcm_coeffs | (lcm_coeffs * x))
                lcm_divs = lcm (lcm_divs, lcm_coeffs);

                TRACE ("qe",
                        tout << "lcm of coeffs: " << lcm_coeffs << "\n";
                        tout << "lcm of divs: " << lcm_divs << "\n";
                      );
            }

            expr_ref z (a.mk_numeral (rational::zero (), a.mk_int ()), m);
            expr_ref x_term_val (m);

            // use equality term
            if (eq_idx < lits.size ()) {
                if (a.is_real (m_var->x ())) {
                    // c*x + t = 0  <=>  x = -t/c
                    expr_ref eq_term (mk_mul (-(rational::one ()/m_coeffs[eq_idx]), m_terms.get (eq_idx)), m);
                    m_rw (eq_term);
                    map.insert (m_var->x (), eq_term, nullptr);
                    TRACE ("qe",
                            tout << "Using equality term: " << mk_pp (eq_term, m) << "\n";
                          );
                }
                else {
                    // find substitution term for (lcm_coeffs * x)
                    if (m_coeffs[eq_idx].is_pos ()) {
                        x_term_val = a.mk_uminus (m_terms.get (eq_idx));
                    } else {
                        x_term_val = m_terms.get (eq_idx);
                    }
                    m_rw (x_term_val);
                    TRACE ("qe",
                            tout << "Using equality literal: " << mk_pp (m_lits.get (eq_idx), m) << "\n";
                            tout << "substitution for (lcm_coeffs * x): " << mk_pp (x_term_val, m) << "\n";
                          );
                    // can't simply substitute for x; need to explicitly substitute the lits
                    mk_lit_substitutes (x_term_val, map, eq_idx);

                    if (!lcm_coeffs.is_one ()) {
                        // new div constraint: lcm_coeffs | x_term_val
                        div_lit = m.mk_eq (a.mk_mod (x_term_val,
                                                     a.mk_numeral (lcm_coeffs, a.mk_int ())),
                                           z);
                    }
                }

                return true;
            }

            expr_ref new_lit (m);

            if (num_pos == 0 || num_neg == 0) {
                TRACE ("qe",
                        if (num_pos == 0) {
                            tout << "virtual substitution with +infinity\n";
                        } else {
                            tout << "virtual substitution with -infinity\n";
                        }
                      );

                /**
                 * make all equalities false;
                 * if num_pos = 0 (num_neg = 0), make all positive (negative) inequalities false;
                 * make the rest inequalities true;
                 * substitute value of x under given model for the rest (div terms)
                 */

                if (a.is_int (m_var->x())) {
                    // to substitute for (lcm_coeffs * x), it suffices to pick
                    // some element in the congruence class of (lcm_coeffs * x) mod lcm_divs;
                    // simply substituting var_val for x in the literals does this job;
                    // but to keep constants small, we use (lcm_coeffs * var_val) % lcm_divs instead
                    rational var_val_num;
                    VERIFY (a.is_numeral (var_val, var_val_num));
                    x_term_val = a.mk_numeral (mod (lcm_coeffs * var_val_num, lcm_divs),
                                               a.mk_int ());
                    TRACE ("qe",
                            tout << "Substitution for (lcm_coeffs * x): "
                                 << mk_pp (x_term_val, m) << "\n";
                          );
                }
                for (unsigned i = 0; i < m_lits.size (); i++) {
                    if (!m_divs[i].is_zero ()) {
                        // m_divs[i] | (x_term_val + m_terms[i])

                      // -- x_term_val is the absolute value, negate it if needed
                      if (m_coeffs.get (i).is_pos ())
                        new_lit = a.mk_add (m_terms.get (i), x_term_val);
                      else
                        new_lit = a.mk_add (m_terms.get (i), a.mk_uminus (x_term_val));

                      // XXX Our handling of divisibility constraints is very fragile.
                      // XXX Rewrite before applying divisibility to preserve syntactic structure
                      m_rw(new_lit);
                      new_lit = m.mk_eq (a.mk_mod (new_lit,
                                                   a.mk_numeral (m_divs[i], a.mk_int ())), z);
                    } else if (m_eq[i] ||
                               (num_pos == 0 && m_coeffs[i].is_pos ()) ||
                               (num_neg == 0 && m_coeffs[i].is_neg ())) {
                        new_lit = m.mk_false ();
                    } else {
                        new_lit = m.mk_true ();
                    }
                    map.insert (m_lits.get (i), new_lit, nullptr);
                    TRACE ("qe",
                            tout << "Old literal: " << mk_pp (m_lits.get (i), m) << "\n";
                            tout << "New literal: " << mk_pp (new_lit, m) << "\n";
                          );
                }
                return true;
            }

            bool use_pos = num_pos < num_neg; // pick a side; both are sound

            unsigned max_t = find_max(mdl, use_pos);

            TRACE ("qe",
                    if (use_pos) {
                        tout << "virtual substitution with upper bound:\n";
                    } else {
                        tout << "virtual substitution with lower bound:\n";
                    }
                    tout << "test point: " << mk_pp (m_lits.get (max_t), m) << "\n";
                    tout << "coeff: " << m_coeffs[max_t] << "\n";
                    tout << "term: " << mk_pp (m_terms.get (max_t), m) << "\n";
                    tout << "is_strict: " << m_strict[max_t] << "\n";
                  );

            if (a.is_real (m_var->x ())) {
                for (unsigned i = 0; i < m_lits.size(); ++i) {
                    if (i != max_t) {
                        if (m_eq[i]) {
                            if (!m_strict[max_t]) {
                                new_lit = mk_eq (i, max_t);
                            } else {
                                new_lit = m.mk_false ();
                            }
                        } else if (m_coeffs[i].is_pos() == use_pos) {
                            new_lit = mk_le (i, max_t);
                        } else {
                            new_lit = mk_lt (i, max_t);
                        }
                    } else {
                        new_lit = m.mk_true ();
                    }
                    map.insert (m_lits.get (i), new_lit, nullptr);
                    TRACE ("qe",
                            tout << "Old literal: " << mk_pp (m_lits.get (i), m) << "\n";
                            tout << "New literal: " << mk_pp (new_lit, m) << "\n";
                          );
                }
            } else {
                SASSERT (a.is_int (m_var->x ()));

                // mk substitution term for (lcm_coeffs * x)

                // evaluate c*x + t for the literal at max_t
                expr_ref cx (m), cxt (m), val (m);
                rational r;
                cx = mk_mul (m_coeffs[max_t], m_var->x());
                cxt = mk_add (cx, m_terms.get (max_t));
                VERIFY(mdl.eval(cxt, val, true));
                VERIFY(a.is_numeral(val, r));

                // get the offset from the smallest/largest possible value for x
                // literal      smallest/largest val of x
                // -------      --------------------------
                // l < x            l+1
                // l <= x            l
                // x < u            u-1
                // x <= u            u
                rational offset;
                if (m_strict[max_t]) {
                    offset = abs(r) - rational::one ();
                } else {
                    offset = abs(r);
                }
                // obtain the offset modulo lcm_divs
                offset %= lcm_divs;

                // for strict negative literal (i.e. strict lower bound),
                // substitution term is (t+1+offset); for non-strict, it's (t+offset)
                //
                // for positive term, subtract from 0
                x_term_val = mk_add (m_terms.get (max_t), a.mk_numeral (offset, a.mk_int ()));
                if (m_strict[max_t]) {
                    x_term_val = a.mk_add (x_term_val, a.mk_numeral (rational::one(), a.mk_int ()));
                }
                if (m_coeffs[max_t].is_pos ()) {
                    x_term_val = a.mk_uminus (x_term_val);
                }
                m_rw (x_term_val);

                TRACE ("qe",
                        tout << "substitution for (lcm_coeffs * x): " << mk_pp (x_term_val, m) << "\n";
                      );

                // obtain substitutions for all literals in map
                mk_lit_substitutes (x_term_val, map, max_t);

                if (!lcm_coeffs.is_one ()) {
                    // new div constraint: lcm_coeffs | x_term_val
                    div_lit = m.mk_eq (a.mk_mod (x_term_val,
                                                 a.mk_numeral (lcm_coeffs, a.mk_int ())),
                                       z);
                }
            }
            return true;
        }

        unsigned find_max(model& mdl, bool do_pos) {
            unsigned result = UINT_MAX;
            bool found = false;
            bool found_strict = false;
            rational found_val (0), r, r_plus_x, found_c;
            expr_ref val(m);

            // evaluate x in mdl
            rational r_x;
            VERIFY(mdl.eval(m_var->x (), val, true));
            VERIFY(a.is_numeral (val, r_x));

            for (unsigned i = 0; i < m_terms.size(); ++i) {
                rational const& ac = m_coeffs[i];
                if (!m_eq[i] && ac.is_pos() == do_pos) {
                    VERIFY(mdl.eval(m_terms.get (i), val, true));
                    VERIFY(a.is_numeral(val, r));
                    r /= abs(ac);
                    // skip the literal if false in the model
                    if (do_pos) { r_plus_x = r + r_x; }
                    else { r_plus_x = r - r_x; }
                    if (!((m_strict[i] && r_plus_x < rational::zero ()) ||
                            (!m_strict[i] && r_plus_x <= rational::zero ()))) {
                        continue;
                    }
                    IF_VERBOSE(2, verbose_stream() << "max: " << mk_pp(m_terms.get (i), m) << " " << r << " " <<
                                (!found || r > found_val || (r == found_val && !found_strict && m_strict[i])) << "\n";);
                    if (!found || r > found_val || (r == found_val && !found_strict && m_strict[i])) {
                        result = i;
                        found_val = r;
                        found_c = ac;
                        found = true;
                        found_strict = m_strict[i];
                    }
                }
            }
            SASSERT(found);
            return result;
        }

        // ax + t <= 0
        // bx + s <= 0
        // a and b have different signs.
        // Infer: a|b|x + |b|t + |a|bx + |a|s <= 0
        // e.g.   |b|t + |a|s <= 0
        expr_ref mk_lt(unsigned i, unsigned j) {
            rational const& ac = m_coeffs[i];
            rational const& bc = m_coeffs[j];
            SASSERT(ac.is_pos() != bc.is_pos());
            SASSERT(ac.is_neg() != bc.is_neg());
            expr_ref bt (m), as (m), ts (m), z (m);
            expr* t = m_terms.get (i);
            expr* s = m_terms.get (j);
            bt = mk_mul(abs(bc), t);
            as = mk_mul(abs(ac), s);
            ts = mk_add(bt, as);
            z  = a.mk_numeral(rational(0), m.get_sort(t));
            expr_ref result1(m), result2(m);
            if (m_strict[i] || m_strict[j]) {
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
            rational const& ac = m_coeffs[i];
            rational const& bc = m_coeffs[j];
            SASSERT(ac.is_pos() == bc.is_pos());
            SASSERT(ac.is_neg() == bc.is_neg());
            expr_ref bt (m), as (m);
            expr* t = m_terms.get (i);
            expr* s = m_terms.get (j);
            bt = mk_mul(abs(bc), t);
            as = mk_mul(abs(ac), s);
            expr_ref result1(m), result2(m);
            if (!m_strict[j] && m_strict[i]) {
                result1 = a.mk_lt(bt, as);
            }
            else {
                result1 = a.mk_le(bt, as);
            }
            m_rw(result1, result2);
            return result2;
        }

        // ax + t = 0
        // bx + s <= 0
        // replace equality by (-t/a == -s/b), or, as = bt
        expr_ref mk_eq (unsigned i, unsigned j) {
            expr_ref as (m), bt (m);
            as = mk_mul (m_coeffs[i], m_terms.get (j));
            bt = mk_mul (m_coeffs[j], m_terms.get (i));
            expr_ref result (m);
            result = m.mk_eq (as, bt);
            m_rw (result);
            return result;
        }


        expr* mk_add(expr* t1, expr* t2) {
            return a.mk_add(t1, t2);
        }
        expr* mk_mul(rational const& r, expr* t2) {
            expr* t1 = a.mk_numeral(r, m.get_sort(t2));
            return a.mk_mul(t1, t2);
        }

        /**
         * walk the ast of fml and introduce a fresh variable for every mod term
         * (updating the mdl accordingly)
         */
        void factor_mod_terms (expr_ref& fml, app_ref_vector& vars, model& mdl) {
            expr_ref_vector todo (m), eqs (m);
            expr_map factored_terms (m);
            ast_mark done;

            todo.push_back (fml);
            while (!todo.empty ()) {
                expr* e = todo.back ();
                if (!is_app (e) || done.is_marked (e)) {
                    todo.pop_back ();
                    continue;
                }
                app* ap = to_app (e);
                unsigned num_args = ap->get_num_args ();
                bool all_done = true, changed = false;
                expr_ref_vector args (m);
                for (unsigned i = 0; i < num_args; i++) {
                    expr* old_arg = ap->get_arg (i);
                    if (!done.is_marked (old_arg)) {
                        todo.push_back (old_arg);
                        all_done = false;
                    }
                    if (!all_done) continue;
                    // all args so far have been processed
                    // get the correct arg to use
                    proof* pr = nullptr; expr* new_arg = nullptr;
                    factored_terms.get (old_arg, new_arg, pr);
                    if (new_arg) {
                        // changed
                        args.push_back (new_arg);
                        changed = true;
                    }
                    else {
                        // not changed
                        args.push_back (old_arg);
                    }
                }
                if (all_done) {
                    // all args processed; make new term
                    func_decl* d = ap->get_decl ();
                    expr_ref new_term (m);
                    new_term = m.mk_app (d, args.size (), args.c_ptr ());
                    // check for mod and introduce new var
                    if (a.is_mod (ap)) {
                        app_ref new_var (m);
                        new_var = m.mk_fresh_const ("mod_var", d->get_range ());
                        eqs.push_back (m.mk_eq (new_var, new_term));
                        // obtain value of new_term in mdl
                        expr_ref val (m);
                        mdl.eval (new_term, val, true);
                        // use the variable from now on
                        new_term = new_var;
                        changed = true;
                        // update vars and mdl
                        vars.push_back (new_var);
                        mdl.register_decl (new_var->get_decl (), val);
                    }
                    if (changed) {
                        factored_terms.insert (e, new_term, nullptr);
                    }
                    done.mark (e, true);
                    todo.pop_back ();
                }
            }

            // mk new fml
            proof* pr = nullptr; expr* new_fml = nullptr;
            factored_terms.get (fml, new_fml, pr);
            if (new_fml) {
                fml = new_fml;
                // add in eqs
                fml = m.mk_and (fml, m.mk_and (eqs.size (), eqs.c_ptr ()));
            }
            else {
                // unchanged
                SASSERT (eqs.empty ());
            }
        }

        /**
         * factor out mod terms by using divisibility terms;
         *
         * for now, only handle mod equalities of the form (t1 % num == t2),
         * replacing it by the equivalent (num | (t1-t2)) /\ (0 <= t2 < abs(num));
         * the divisibility atom is a special mod term ((t1-t2) % num == 0)
         */
        void mod2div (expr_ref& fml, expr_map& map) {
            expr* new_fml = nullptr;

            proof *pr = nullptr;
            map.get (fml, new_fml, pr);
            if (new_fml) {
                fml = new_fml;
                return;
            }

            expr_ref z (a.mk_numeral (rational::zero (), a.mk_int ()), m);
            bool is_mod_eq = false;

            expr *e1, *e2, *num;
            expr_ref t1 (m), t2 (m);
            rational num_val;
            bool is_int;
            // check if fml is a mod equality (t1 % num) == t2
            if (m.is_eq (fml, e1, e2)) {
                expr* t;
                if (a.is_mod (e1, t, num) && a.is_numeral (num, num_val, is_int) && is_int) {
                    t1 = t;
                    t2 = e2;
                    is_mod_eq = true;
                } else if (a.is_mod (e2, t, num) && a.is_numeral (num, num_val, is_int) && is_int) {
                    t1 = t;
                    t2 = e1;
                    is_mod_eq = true;
                }
            }

            if (is_mod_eq) {
                // recursively mod2div for t1 and t2
                mod2div (t1, map);
                mod2div (t2, map);

                rational t2_num;
                if (a.is_numeral (t2, t2_num) && t2_num.is_zero ()) {
                    // already in the desired form;
                    // new_fml is (num_val | t1)
                    new_fml = m.mk_eq (a.mk_mod (t1, a.mk_numeral (num_val, a.mk_int ())),
                                       z);
                }
                else {
                    expr_ref_vector lits (m);
                    // num_val | (t1 - t2)
                    lits.push_back (m.mk_eq (a.mk_mod (a.mk_sub (t1, t2),
                                                    a.mk_numeral (num_val, a.mk_int ())),
                                          z));
                    // 0 <= t2
                    lits.push_back (a.mk_le (z, t2));
                    // t2 < abs (num_val)
                    lits.push_back (a.mk_lt (t2, a.mk_numeral (abs (num_val), a.mk_int ())));

                    new_fml = m.mk_and (lits.size (), lits.c_ptr ());
                }
            }
            else if (!is_app (fml)) {
                new_fml = fml;
            }
            else {
                app* a = to_app (fml);
                expr_ref_vector children (m);
                expr_ref ch (m);
                for (unsigned i = 0; i < a->get_num_args (); i++) {
                    ch = a->get_arg (i);
                    mod2div (ch, map);
                    children.push_back (ch);
                }
                new_fml = m.mk_app (a->get_decl (), children.size (), children.c_ptr ());
            }

            map.insert (fml, new_fml, nullptr);
            fml = new_fml;
        }

        void collect_lits (expr* fml, app_ref_vector& lits) {
            expr_ref_vector todo (m);
            ast_mark visited;
            todo.push_back(fml);
            while (!todo.empty()) {
                expr* e = todo.back();
                todo.pop_back();
                if (visited.is_marked(e)) {
                    continue;
                }
                visited.mark(e, true);
                if (!is_app(e)) {
                    continue;
                }
                app* a = to_app(e);
                if (m.is_and(a) || m.is_or(a)) {
                    for (unsigned i = 0; i < a->get_num_args(); ++i) {
                        todo.push_back(a->get_arg(i));
                    }
                } else {
                    lits.push_back (a);
                }
            }
            SASSERT(todo.empty());
            visited.reset();
        }

        /**
         * assume that all coeffs of x are the same, say c
         * substitute x_term_val for (c*x) in all lits and update map
         * make the literal at idx true
         */
        void mk_lit_substitutes (expr_ref const& x_term_val, expr_map& map, unsigned idx) {
            expr_ref z (a.mk_numeral (rational::zero (), a.mk_int ()), m);
            expr_ref cxt (m), new_lit (m);
            for (unsigned i = 0; i < m_lits.size(); ++i) {
                if (i == idx) {
                    new_lit = m.mk_true ();
                } else {
                    // cxt
                    if (m_coeffs[i].is_neg ()) {
                        cxt = a.mk_sub (m_terms.get (i), x_term_val);
                    } else {
                        cxt = a.mk_add (m_terms.get (i), x_term_val);
                    }

                    if (m_divs[i].is_zero ()) {
                        if (m_eq[i]) {
                            new_lit = m.mk_eq (cxt, z);
                        } else if (m_strict[i]) {
                            new_lit = a.mk_lt (cxt, z);
                        } else {
                            new_lit = a.mk_le (cxt, z);
                        }
                        m_rw(new_lit);
                    } else {
                        // div term
                        // XXX rewrite before applying mod to ensure mod is the top-level operator
                        m_rw(cxt);
                        new_lit = m.mk_eq (a.mk_mod (cxt,
                                                     a.mk_numeral (m_divs[i], a.mk_int ())),
                                           z);
                    }
                }
                map.insert (m_lits.get (i), new_lit, nullptr);
                TRACE ("qe",
                        tout << "Old literal: " << mk_pp (m_lits.get (i), m) << "\n";
                        tout << "New literal: " << mk_pp (new_lit, m) << "\n";
                      );
            }
        }

        void substitute (expr_ref& fml, app_ref_vector& lits, expr_map& map) {
            expr_substitution sub (m);
            // literals
            for (unsigned i = 0; i < lits.size (); i++) {
                expr* new_lit = nullptr; proof* pr = nullptr;
                app* old_lit = lits.get (i);
                map.get (old_lit, new_lit, pr);
                if (new_lit) {
                    sub.insert (old_lit, new_lit);
                    TRACE ("qe",
                            tout << "old lit " << mk_pp (old_lit, m) << "\n";
                            tout << "new lit " << mk_pp (new_lit, m) << "\n";
                          );
                }
            }
            // substitute for x, if any
            expr* x_term = nullptr; proof* pr = nullptr;
            map.get (m_var->x (), x_term, pr);
            if (x_term) {
                sub.insert (m_var->x (), x_term);
                TRACE ("qe",
                        tout << "substituting " << mk_pp (m_var->x (), m) << " by " << mk_pp (x_term, m) << "\n";
                      );
            }
            scoped_ptr<expr_replacer> rep = mk_default_expr_replacer (m);
            rep->set_substitution (&sub);
            (*rep)(fml);
        }

    public:
        arith_project_util(ast_manager& m):
            m(m), a(m), m_rw(m), m_lits (m), m_terms (m) {}

        // OLD AND UNUSED INTERFACE
        expr_ref operator()(model& mdl, app_ref_vector& vars, expr_ref_vector const& lits) {
            app_ref_vector new_vars(m);
            expr_ref_vector result(lits);
            for (unsigned i = 0; i < vars.size(); ++i) {
                app* v = vars.get (i);
                m_var = alloc(contains_app, m, v);
                bool fail = a.is_int (v) || !project (mdl, result);
                if (fail) new_vars.push_back (v);

                IF_VERBOSE(2,
                        if (fail) {
                            verbose_stream() << "can't project:" << mk_pp(v, m) << "\n";
                        }
                );
                TRACE("qe",
                        if (!fail) {
                            tout << "projected: " << mk_pp(v, m) << "\n";
                            for (unsigned i = 0; i < result.size(); ++i) {
                                tout << mk_pp(result.get (i), m) << "\n";
                            }
                        }
                        else {
                            tout << "Failed to project: " << mk_pp (v, m) << "\n";
                        }
                     );
            }
            vars.reset();
            vars.append(new_vars);
            return mk_and(result);
        }

        void operator()(model& mdl, app_ref_vector& vars, expr_ref& fml) {
          expr_map map (m);
            operator()(mdl, vars, fml, map);
        }

        void operator()(model& mdl, app_ref_vector& vars, expr_ref& fml, expr_map& map) {
            app_ref_vector new_vars(m);

            // factor out mod terms by introducing new variables
            TRACE ("qe",
                    tout << "before factoring out mod terms:" << "\n";
                    tout << mk_pp (fml, m) << "\n";
                    tout << "mdl:\n";
                    model_pp (tout, mdl);
                    tout << "\n";
                  );

            factor_mod_terms (fml, vars, mdl);

            TRACE ("qe",
                    tout << "after factoring out mod terms:" << "\n";
                    tout << mk_pp (fml, m) << "\n";
                    tout << "updated mdl:\n";
                    model_pp (tout, mdl);
                    tout << "\n";
                  );

            app_ref_vector lits (m);
//          expr_map map (m);
            for (unsigned i = 0; i < vars.size(); ++i) {
                app* v = vars.get (i);
                TRACE ("qe",
                        tout << "projecting variable: " << mk_pp (v, m) << "\n";
                      );
                m_var = alloc(contains_app, m, v);
                map.reset ();
                lits.reset ();
                if (a.is_int (v)) {
                    // factor out mod terms using div terms
                    expr_map mod_map (m);
                    mod2div (fml, mod_map);
                    TRACE ("qe",
                            tout << "after mod2div:" << "\n";
                            tout << mk_pp (fml, m) << "\n";
                          );
                }
                collect_lits (fml, lits);
                app_ref div_lit (m);
                if (project (mdl, lits, map, div_lit)) {
                    substitute (fml, lits, map);
                    if (div_lit) {
                        fml = m.mk_and (fml, div_lit);
                    }
                    TRACE("qe",
                            tout << "projected: " << mk_pp(v, m) << " "
                                 << mk_pp(fml, m) << "\n";
                         );
                }
                else {
                    IF_VERBOSE(2, verbose_stream() << "can't project:" << mk_pp(v, m) << "\n";);
                    TRACE ("qe", tout << "Failed to project: " << mk_pp (v, m) << "\n";);
                    new_vars.push_back(v);
                }
            }
            vars.reset();
            vars.append(new_vars);
            m_rw (fml);
        }
    };


    class array_project_eqs_util {
        ast_manager&                m;
        array_util                  m_arr_u;
        model_ref                   M;
        app_ref                     m_v;    // array var to eliminate
        ast_mark                    m_has_stores_v; // has stores for m_v
        expr_ref                    m_subst_term_v; // subst term for m_v
        expr_safe_replace           m_true_sub_v; // subst for true equalities
        expr_safe_replace           m_false_sub_v; // subst for false equalities
        expr_ref_vector             m_aux_lits_v;
        expr_ref_vector             m_idx_lits_v;
        app_ref_vector              m_aux_vars;
        model_evaluator_array_util  m_mev;

        void reset_v () {
            m_v = nullptr;
            m_has_stores_v.reset ();
            m_subst_term_v = nullptr;
            m_true_sub_v.reset ();
            m_false_sub_v.reset ();
            m_aux_lits_v.reset ();
            m_idx_lits_v.reset ();
        }

        void reset () {
            M = nullptr;
            reset_v ();
            m_aux_vars.reset ();
        }

        /**
         * find all array equalities on m_v or containing stores on/of m_v
         *
         * also mark terms containing stores on/of m_v
         */
        void find_arr_eqs (expr_ref const& fml, expr_ref_vector& eqs) {
            if (!is_app (fml)) return;
            ast_mark done;
            ptr_vector<app> todo;
            todo.push_back (to_app (fml));
            while (!todo.empty ()) {
                app* a = todo.back ();
                if (done.is_marked (a)) {
                    todo.pop_back ();
                    continue;
                }
                bool all_done = true;
                bool args_have_stores = false;
                unsigned num_args = a->get_num_args ();
                for (unsigned i = 0; i < num_args; i++) {
                    expr* arg = a->get_arg (i);
                    if (!is_app (arg)) continue;
                    if (!done.is_marked (arg)) {
                        all_done = false;
                        todo.push_back (to_app (arg));
                    }
                    else if (!args_have_stores && m_has_stores_v.is_marked (arg)) {
                        args_have_stores = true;
                    }
                }
                if (!all_done) continue;
                todo.pop_back ();

                // mark if a has stores
                if ((!m_arr_u.is_select (a) && args_have_stores) ||
                        (m_arr_u.is_store (a) && (a->get_arg (0) == m_v))) {
                    m_has_stores_v.mark (a, true);

                    TRACE ("qe",
                            tout << "has stores:\n";
                            tout << mk_pp (a, m) << "\n";
                          );
                }

                // check if a is a relevant array equality
                if (m.is_eq (a)) {
                    expr* a0 = to_app (a)->get_arg (0);
                    expr* a1 = to_app (a)->get_arg (1);
                    if (a0 == m_v || a1 == m_v ||
                            (m_arr_u.is_array (a0) && m_has_stores_v.is_marked (a))) {
                        eqs.push_back (a);
                    }
                }
                // else, we can check for disequalities and handle them using extensionality,
                // but it's not necessary

                done.mark (a, true);
            }
        }

        /**
         * factor out select terms on m_v using fresh consts
         */
        void factor_selects (app_ref& fml) {
            expr_map sel_cache (m);
            ast_mark done;
            ptr_vector<app> todo;
            expr_ref_vector pinned (m); // to ensure a reference

            todo.push_back (fml);
            while (!todo.empty ()) {
                app* a = todo.back ();
                if (done.is_marked (a)) {
                    todo.pop_back ();
                    continue;
                }
                expr_ref_vector args (m);
                bool all_done = true;
                for (unsigned i = 0; i < a->get_num_args (); i++) {
                    expr* arg = a->get_arg (i);
                    if (!is_app (arg)) continue;
                    if (!done.is_marked (arg)) {
                        all_done = false;
                        todo.push_back (to_app (arg));
                    }
                    else if (all_done) { // all done so far..
                        expr* arg_new = nullptr; proof* pr;
                        sel_cache.get (arg, arg_new, pr);
                        if (!arg_new) {
                            arg_new = arg;
                        }
                        args.push_back (arg_new);
                    }
                }
                if (!all_done) continue;
                todo.pop_back ();

                expr_ref a_new (m.mk_app (a->get_decl (), args.size (), args.c_ptr ()), m);

                // if a_new is select on m_v, introduce new constant
                if (m_arr_u.is_select (a) &&
                        (args.get (0) == m_v || m_has_stores_v.is_marked (args.get (0)))) {
                    sort* val_sort = get_array_range (m.get_sort (m_v));
                    app_ref val_const (m.mk_fresh_const ("sel", val_sort), m);
                    m_aux_vars.push_back (val_const);
                    // extend M to include val_const
                    expr_ref val (m);
                    m_mev.eval (*M, a_new, val);
                    M->register_decl (val_const->get_decl (), val);
                    // add equality
                    m_aux_lits_v.push_back (m.mk_eq (val_const, a_new));
                    // replace select by const
                    a_new = val_const;
                }

                if (a != a_new) {
                    sel_cache.insert (a, a_new, nullptr);
                    pinned.push_back (a_new);
                }
                done.mark (a, true);
            }
            expr* res = nullptr; proof* pr;
            sel_cache.get (fml, res, pr);
            if (res) {
                fml = to_app (res);
            }
        }

        /**
         * convert partial equality expression p_exp to an equality by
         * recursively adding stores on diff indices
         *
         * add stores on lhs or rhs depending on whether stores_on_rhs is false/true
         */
        void convert_peq_to_eq (expr* p_exp, app_ref& eq, bool stores_on_rhs = true) {
            peq p (to_app (p_exp), m);
            app_ref_vector diff_val_consts (m);
            p.mk_eq (diff_val_consts, eq, stores_on_rhs);
            m_aux_vars.append (diff_val_consts);
            // extend M to include diff_val_consts
            expr_ref arr (m);
            expr_ref_vector I (m);
            p.lhs (arr);
            p.get_diff_indices (I);
            expr_ref val (m);
            unsigned num_diff = diff_val_consts.size ();
            SASSERT (num_diff == I.size ());
            for (unsigned i = 0; i < num_diff; i++) {
                // mk val term
                ptr_vector<expr> sel_args;
                sel_args.push_back (arr);
                sel_args.push_back (I.get (i));
                expr_ref val_term (m_arr_u.mk_select (sel_args.size (), sel_args.c_ptr ()), m);
                // evaluate and assign to ith diff_val_const
                m_mev.eval (*M, val_term, val);
                M->register_decl (diff_val_consts.get (i)->get_decl (), val);
            }
        }

        /**
         * mk (e0 ==indices e1)
         *
         * result has stores if either e0 or e1 or an index term has stores
         */
        void mk_peq (expr* e0, expr* e1, unsigned num_indices, expr* const* indices, app_ref& result) {
            peq p (e0, e1, num_indices, indices, m);
            p.mk_peq (result);
        }

        void find_subst_term (app* eq) {
            app_ref p_exp (m);
            mk_peq (eq->get_arg (0), eq->get_arg (1), 0, nullptr, p_exp);
            bool subst_eq_found = false;
            while (true) {
                TRACE ("qe",
                        tout << "processing peq:\n";
                        tout << mk_pp (p_exp, m) << "\n";
                      );

                peq p (p_exp, m);
                expr_ref lhs (m), rhs (m);
                p.lhs (lhs); p.rhs (rhs);
                if (!m_has_stores_v.is_marked (lhs)) {
                    std::swap (lhs, rhs);
                }
                if (m_has_stores_v.is_marked (lhs)) {
                    /** project using the equivalence:
                     *
                     *  (store(arr0,idx,x) ==I arr1) <->
                     *
                     *  (idx \in I => (arr0 ==I arr1)) /\
                     *  (idx \not\in I => (arr0 ==I+idx arr1) /\ (arr1[idx] == x)))
                     */
                    expr_ref_vector I (m);
                    p.get_diff_indices (I);
                    app* a_lhs = to_app (lhs);
                    expr* arr0 = a_lhs->get_arg (0);
                    expr* idx = a_lhs->get_arg (1);
                    expr* x = a_lhs->get_arg (2);
                    expr* arr1 = rhs;
                    // check if (idx \in I) in M
                    bool idx_in_I = false;
                    expr_ref_vector idx_diseq (m);
                    if (!I.empty ()) {
                        expr_ref val (m);
                        m_mev.eval (*M, idx, val);
                        for (unsigned i = 0; i < I.size () && !idx_in_I; i++) {
                            if (idx == I.get (i)) {
                                idx_in_I = true;
                            }
                            else {
                                expr_ref val1 (m);
                                expr* idx1 = I.get (i);
                                expr_ref idx_eq (m.mk_eq (idx, idx1), m);
                                m_mev.eval (*M, idx1, val1);
                                if (val == val1) {
                                    idx_in_I = true;
                                    m_idx_lits_v.push_back (idx_eq);
                                }
                                else {
                                    idx_diseq.push_back (m.mk_not (idx_eq));
                                }
                            }
                        }
                    }
                    if (idx_in_I) {
                        TRACE ("qe",
                                tout << "store index in diff indices:\n";
                                tout << mk_pp (m_idx_lits_v.back (), m) << "\n";
                              );

                        // arr0 ==I arr1
                        mk_peq (arr0, arr1, I.size (), I.c_ptr (), p_exp);

                        TRACE ("qe",
                                tout << "new peq:\n";
                                tout << mk_pp (p_exp, m) << "\n";
                              );
                    }
                    else {
                        m_idx_lits_v.append (idx_diseq);
                        // arr0 ==I+idx arr1
                        I.push_back (idx);
                        mk_peq (arr0, arr1, I.size (), I.c_ptr (), p_exp);

                        TRACE ("qe",
                                tout << "new peq:\n";
                                tout << mk_pp (p_exp, m) << "\n";
                              );

                        // arr1[idx] == x
                        ptr_vector<expr> sel_args;
                        sel_args.push_back (arr1);
                        sel_args.push_back (idx);
                        expr_ref arr1_idx (m_arr_u.mk_select (sel_args.size (), sel_args.c_ptr ()), m);
                        expr_ref eq (m.mk_eq (arr1_idx, x), m);
                        m_aux_lits_v.push_back (eq);

                        TRACE ("qe",
                                tout << "new eq:\n";
                                tout << mk_pp (eq, m) << "\n";
                              );
                    }
                }
                else if (lhs == rhs) { // trivial peq (a ==I a)
                    break;
                }
                else if (lhs == m_v || rhs == m_v) {
                    subst_eq_found = true;
                    TRACE ("qe",
                            tout << "subst eq found!\n";
                          );
                    break;
                }
                else {
                    UNREACHABLE ();
                }
            }

            // factor out select terms on m_v from p_exp using fresh constants
            if (subst_eq_found) {
                factor_selects (p_exp);

                TRACE ("qe",
                        tout << "after factoring selects:\n";
                        tout << mk_pp (p_exp, m) << "\n";
                        for (unsigned i = m_aux_lits_v.size () - m_aux_vars.size (); i < m_aux_lits_v.size (); i++) {
                            tout << mk_pp (m_aux_lits_v.get (i), m) << "\n";
                        }
                      );

                // find subst_term
                bool stores_on_rhs = true;
                app* a = to_app (p_exp);
                if (a->get_arg (1) == m_v) {
                    stores_on_rhs = false;
                }
                app_ref eq (m);
                convert_peq_to_eq (p_exp, eq, stores_on_rhs);
                m_subst_term_v = eq->get_arg (1);

                TRACE ("qe",
                        tout << "subst term found:\n";
                        tout << mk_pp (m_subst_term_v, m) << "\n";
                      );
            }
        }

        /**
         * try to substitute for m_v, using array equalities
         *
         * compute substitution term and aux lits
         */
        bool project (expr_ref const& fml) {
            expr_ref_vector eqs (m);
            ptr_vector<app> true_eqs; // subset of eqs; eqs ensures references

            find_arr_eqs (fml, eqs);
            TRACE ("qe",
                    tout << "array equalities:\n";
                    for (unsigned i = 0; i < eqs.size (); i++) {
                        tout << mk_pp (eqs.get (i), m) << "\n";
                    }
                  );

            // evaluate eqs in M
            for (unsigned i = 0; i < eqs.size (); i++) {
                TRACE ("qe",
                        tout << "array equality:\n";
                        tout << mk_pp (eqs.get (i), m) << "\n";
                      );

                expr* eq = eqs.get (i);

                // evaluate eq in M
                app* a = to_app (eq);
                expr_ref val (m);
                m_mev.eval_array_eq (*M, a, a->get_arg (0), a->get_arg (1), val);
                if (!val) {
                    // XXX HACK: unable to evaluate. set to true?
                    val = m.mk_true ();
                }
                SASSERT (m.is_true (val) || m.is_false (val));

                if (m.is_false (val)) {
                    m_false_sub_v.insert (eq, m.mk_false ());
                }
                else {
                    true_eqs.push_back (to_app (eq));
                }
            }

            // compute nesting depths of stores on m_v in true_eqs, as follows:
            // 0 if m_v appears on both sides of equality
            // 1 if equality is (m_v=t)
            // 2 if equality is (store(m_v,i,v)=t)
            // ...
            unsigned num_true_eqs = true_eqs.size ();
            vector<unsigned> nds (num_true_eqs);
            for (unsigned i = 0; i < num_true_eqs; i++) {
                app* eq = true_eqs.get (i);
                expr* lhs = eq->get_arg (0);
                expr* rhs = eq->get_arg (1);
                bool lhs_has_v = (lhs == m_v || m_has_stores_v.is_marked (lhs));
                bool rhs_has_v = (rhs == m_v || m_has_stores_v.is_marked (rhs));
                app* store = nullptr;

                SASSERT (lhs_has_v || rhs_has_v);

                if (!lhs_has_v) {
                    store = to_app (rhs);
                }
                else if (!rhs_has_v) {
                    store = to_app (lhs);
                }
                // else v appears on both sides -- trivial equality
                // put it in the beginning to simplify it away

                unsigned nd = 0; // nesting depth
                if (store) {
                    for (nd = 1; m_arr_u.is_store (store);
                         nd++, store = to_app (store->get_arg (0)))
                      /* empty */ ;
                    SASSERT (store == m_v);
                }
                nds[i] = nd;
            }

            SASSERT (true_eqs.size () == nds.size ());

            // sort true_eqs according to nesting depth
            // use insertion sort
            for (unsigned i = 1; i < num_true_eqs; i++) {
                app_ref eq(m);
                eq = true_eqs.get (i);
                unsigned nd = nds.get (i);
                unsigned j = i;
                for (; j >= 1 && nds.get (j-1) > nd; j--) {
                    true_eqs.set (j, true_eqs.get (j-1));
                    nds.set (j, nds.get (j-1));
                }
                if (j < i) {
                    true_eqs.set (j, eq);
                    nds.set (j, nd);
                    TRACE ("qe",
                            tout << "changing eq order!\n";
                          );
                }
            }

            // search for subst term
            for (unsigned i = 0; !m_subst_term_v && i < num_true_eqs; i++) {
                app* eq = true_eqs.get (i);
                m_true_sub_v.insert (eq, m.mk_true ());
                // try to find subst term
                find_subst_term (eq);
            }

            return true;
        }

        void mk_result (expr_ref& fml) {
            th_rewriter rw(m);
            rw (fml);
            // add in aux_lits and idx_lits
            expr_ref_vector lits (m);
            // TODO: eliminate possible duplicates, especially in idx_lits
            //       theory rewriting is a possibility, but not sure if it
            //          introduces unwanted terms such as ite's
            lits.append (m_idx_lits_v);
            lits.append (m_aux_lits_v);
            lits.push_back (fml);
            fml = m.mk_and (lits.size (), lits.c_ptr ());

            if (m_subst_term_v) {
                m_true_sub_v.insert (m_v, m_subst_term_v);
                m_true_sub_v (fml);
            }
            else {
                m_true_sub_v (fml);
                m_false_sub_v (fml);
            }
            rw(fml);
            SASSERT (!m.is_false (fml));
        }

    public:

        array_project_eqs_util (ast_manager& m):
            m (m),
            m_arr_u (m),
            m_v (m),
            m_subst_term_v (m),
            m_true_sub_v (m),
            m_false_sub_v (m),
            m_aux_lits_v (m),
            m_idx_lits_v (m),
            m_aux_vars (m),
            m_mev (m)
        {}

        void operator () (model& mdl, app_ref_vector& arr_vars, expr_ref& fml, app_ref_vector& aux_vars) {
            reset ();
            app_ref_vector rem_arr_vars (m); // remaining arr vars
            M = &mdl;

            for (unsigned i = 0; i < arr_vars.size (); i++) {
                reset_v ();
                m_v = arr_vars.get (i);
                if (!m_arr_u.is_array (m_v)) {
                    TRACE ("qe",
                            tout << "not an array variable: " << mk_pp (m_v, m) << "\n";
                          );
                    aux_vars.push_back (m_v);
                    continue;
                }
                TRACE ("qe",
                        tout << "projecting equalities on variable: " << mk_pp (m_v, m) << "\n";
                      );

                if (project (fml)) {
                    mk_result (fml);

                    contains_app contains_v (m, m_v);
                    if (!m_subst_term_v || contains_v (m_subst_term_v)) {
                        rem_arr_vars.push_back (m_v);
                    }
                    TRACE ("qe",
                            tout << "after projection: \n";
                            tout << mk_pp (fml, m) << "\n";
                          );
                }
                else {
                    IF_VERBOSE(2, verbose_stream() << "can't project:" << mk_pp(m_v, m) << "\n";);
                    TRACE ("qe", tout << "Failed to project: " << mk_pp (m_v, m) << "\n";);
                    rem_arr_vars.push_back(m_v);
                }
            }
            arr_vars.reset ();
            arr_vars.append (rem_arr_vars);
            aux_vars.append (m_aux_vars);
        }
    };


    class array_select_reducer {
        ast_manager&                m;
        array_util                  m_arr_u;
        obj_map<expr, expr*>        m_cache;
        expr_ref_vector             m_pinned;   // to ensure a reference
        expr_ref_vector             m_idx_lits;
        model_ref                   M;
        model_evaluator_array_util  m_mev;
        th_rewriter                 m_rw;
        ast_mark                    m_arr_test;
        ast_mark                    m_has_stores;
        bool                        m_reduce_all_selects;

        void reset () {
            m_cache.reset ();
            m_pinned.reset ();
            m_idx_lits.reset ();
            M = nullptr;
            m_arr_test.reset ();
            m_has_stores.reset ();
            m_reduce_all_selects = false;
        }

        bool is_equals (expr *e1, expr *e2) {
            if (e1 == e2) return true;
            expr_ref val1 (m), val2 (m);
            m_mev.eval (*M, e1, val1);
            m_mev.eval (*M, e2, val2);
            return (val1 == val2);
        }

        void add_idx_cond (expr_ref& cond) {
            m_rw (cond);
            if (!m.is_true (cond)) m_idx_lits.push_back (cond);
        }

        bool has_stores (expr* e) {
            if (m_reduce_all_selects) return true;
            return m_has_stores.is_marked (e);
        }

        void mark_stores (app* a, bool args_have_stores) {
            if (m_reduce_all_selects) return;
            if (args_have_stores ||
                    (m_arr_u.is_store (a) && m_arr_test.is_marked (a->get_arg (0)))) {
                m_has_stores.mark (a, true);
            }
        }

        bool reduce (expr_ref& e) {
            if (!is_app (e)) return true;

            expr *r = nullptr;
            if (m_cache.find (e, r)) {
                e = r;
                return true;
            }

            ptr_vector<app> todo;
            todo.push_back (to_app (e));

            while (!todo.empty ()) {
                app *a = todo.back ();
                unsigned sz = todo.size ();
                expr_ref_vector args (m);
                bool dirty = false;
                bool args_have_stores = false;

                for (unsigned i = 0; i < a->get_num_args (); ++i) {
                    expr *arg = a->get_arg (i);
                    expr *narg = nullptr;

                    if (!is_app (arg)) args.push_back (arg);
                    else if (m_cache.find (arg, narg)) {
                        args.push_back (narg);
                        dirty |= (arg != narg);
                        if (!args_have_stores && has_stores (narg)) {
                            args_have_stores = true;
                        }
                    }
                    else {
                        todo.push_back (to_app (arg));
                    }
                }

                if (todo.size () > sz) continue;
                todo.pop_back ();

                if (dirty) {
                    r = m.mk_app (a->get_decl (), args.size (), args.c_ptr ());
                    m_pinned.push_back (r);
                }
                else r = a;

                if (m_arr_u.is_select (r) && has_stores (to_app (r)->get_arg (0))) {
                    r = reduce_core (to_app(r));
                }
                else {
                    mark_stores (to_app (r), args_have_stores);
                }

                m_cache.insert (a, r);
            }

            SASSERT (r);
            e = r;
            return true;
        }

        expr* reduce_core (app *a) {
            if (!m_arr_u.is_store (a->get_arg (0))) return a;

            SASSERT (a->get_num_args () == 2 && "Multi-dimensional arrays are not supported");
            expr* array = a->get_arg (0);
            expr* j = a->get_arg (1);

            while (m_arr_u.is_store (array)) {
                a = to_app (array);
                expr* idx = a->get_arg (1);
                expr_ref cond (m);

                if (is_equals (idx, j)) {
                    cond = m.mk_eq (idx, j);
                    add_idx_cond (cond);
                    return a->get_arg (2);
                }
                else {
                    cond = m.mk_not (m.mk_eq (idx, j));
                    add_idx_cond (cond);
                    array = a->get_arg (0);
                }
            }

            expr* args[2] = {array, j};
            expr* r = m_arr_u.mk_select (2, args);
            m_pinned.push_back (r);
            return r;
        }

        void mk_result (expr_ref& fml) {
            // conjoin idx lits
            expr_ref_vector lits (m);
            lits.append (m_idx_lits);
            lits.push_back (fml);
            fml = m.mk_and (lits.size (), lits.c_ptr ());
            // simplify all trivial expressions introduced
            m_rw (fml);

            TRACE ("qe",
                    tout << "after reducing selects:\n";
                    tout << mk_pp (fml, m) << "\n";
                  );
        }

    public:

        array_select_reducer (ast_manager& m):
            m (m),
            m_arr_u (m),
            m_pinned (m),
            m_idx_lits (m),
            m_mev (m),
            m_rw (m),
            m_reduce_all_selects (false)
        {}

        void operator () (model& mdl, app_ref_vector const& arr_vars, expr_ref& fml, bool reduce_all_selects = false) {
            if (!reduce_all_selects && arr_vars.empty ()) return;

            reset ();
            M = &mdl;
            m_reduce_all_selects = reduce_all_selects;

            // mark vars to eliminate
            for (unsigned i = 0; i < arr_vars.size (); i++) {
                m_arr_test.mark (arr_vars.get (i), true);
            }

            // assume all arr_vars are of array sort
            // and assume no store equalities on arr_vars
            if (reduce (fml)) {
                mk_result (fml);
            }
            else {
                IF_VERBOSE(2, verbose_stream() << "can't project arrays:" << "\n";);
                TRACE ("qe", tout << "Failed to project arrays\n";);
            }
        }
    };

    class array_project_selects_util {
        typedef obj_map<app, ptr_vector<app>*> sel_map;

        ast_manager&                m;
        array_util                  m_arr_u;
        arith_util                  m_ari_u;
        sel_map                     m_sel_terms;
        // representative indices for eliminating selects
        expr_ref_vector             m_idx_reprs;
        expr_ref_vector             m_idx_vals;
        app_ref_vector              m_sel_consts;
        expr_ref_vector             m_idx_lits;
        model_ref                   M;
        model_evaluator_array_util  m_mev;
        expr_safe_replace           m_sub;
        ast_mark                    m_arr_test;

        void reset () {
            m_sel_terms.reset ();
            m_idx_reprs.reset ();
            m_idx_vals.reset ();
            m_sel_consts.reset ();
            m_idx_lits.reset ();
            M = nullptr;
            m_sub.reset ();
            m_arr_test.reset ();
        }

        /**
         * collect sel terms on array vars as given by m_arr_test
         */
        void collect_selects (expr* fml) {
            if (!is_app (fml)) return;
            ast_mark done;
            ptr_vector<app> todo;
            todo.push_back (to_app (fml));
            while (!todo.empty ()) {
                app* a = todo.back ();
                if (done.is_marked (a)) {
                    todo.pop_back ();
                    continue;
                }
                unsigned num_args = a->get_num_args ();
                bool all_done = true;
                for (unsigned i = 0; i < num_args; i++) {
                    expr* arg = a->get_arg (i);
                    if (!done.is_marked (arg) && is_app (arg)) {
                        todo.push_back (to_app (arg));
                        all_done = false;
                    }
                }
                if (!all_done) continue;
                todo.pop_back ();
                if (m_arr_u.is_select (a)) {
                    expr* arr = a->get_arg (0);
                    if (m_arr_test.is_marked (arr)) {
                        ptr_vector<app>* lst = m_sel_terms.find (to_app (arr));;
                        lst->push_back (a);
                    }
                }
                done.mark (a, true);
            }
        }

        /**
         * model based ackermannization for sel terms of some array
         *
         * update sub with val consts for sel terms
         */
        void ackermann (ptr_vector<app> const& sel_terms) {
            if (sel_terms.empty ()) return;

            expr* v = sel_terms.get (0)->get_arg (0); // array variable
            sort* v_sort = m.get_sort (v);
            sort* val_sort = get_array_range (v_sort);
            sort* idx_sort = get_array_domain (v_sort, 0);
            (void) idx_sort;

            unsigned start = m_idx_reprs.size (); // append at the end

            for (unsigned i = 0; i < sel_terms.size (); i++) {
                app* a = sel_terms.get (i);
                expr* idx = a->get_arg (1);
                expr_ref val (m);
                m_mev.eval (*M, idx, val);

                bool is_new = true;
                for (unsigned j = start; j < m_idx_vals.size (); j++) {
                    if (m_idx_vals.get (j) == val) {
                        // idx belongs to the jth equivalence class;
                        // substitute sel term with ith sel const
                        expr* c = m_sel_consts.get (j);
                        m_sub.insert (a, c);
                        // add equality (idx == repr)
                        expr* repr = m_idx_reprs.get (j);
                        m_idx_lits.push_back (m.mk_eq (idx, repr));

                        is_new = false;
                        break;
                    }
                }
                if (is_new) {
                    // new repr, val, and sel const
                    m_idx_reprs.push_back (idx);
                    m_idx_vals.push_back (val);
                    app_ref c (m.mk_fresh_const ("sel", val_sort), m);
                    m_sel_consts.push_back (c);
                    // substitute sel term with new const
                    m_sub.insert (a, c);
                    // extend M to include c
                    m_mev.eval (*M, a, val);
                    M->register_decl (c->get_decl (), val);
                }
            }

            // sort reprs by their value and add a chain of strict inequalities

            unsigned num_reprs = m_idx_reprs.size () - start;
            if (num_reprs == 0) return;

            SASSERT ((m_ari_u.is_real (idx_sort) || m_ari_u.is_int (idx_sort))
                        && "Unsupported index sort: neither real nor int");

            // using insertion sort
            unsigned end = start + num_reprs;
            for (unsigned i = start+1; i < end; i++) {
                expr_ref repr(m), val(m);
                repr = m_idx_reprs.get (i);
                val = m_idx_vals.get (i);
                unsigned j = i;
                for (; j > start; j--) {
                    rational j_val, jm1_val;
                    VERIFY (m_ari_u.is_numeral (val, j_val));
                    VERIFY (m_ari_u.is_numeral (m_idx_vals.get (j-1), jm1_val));
                    if (j_val >= jm1_val) break;
                    m_idx_reprs[j] = m_idx_reprs.get (j-1);
                    m_idx_vals[j] = m_idx_vals.get (j-1);
                }
                m_idx_reprs[j] = repr;
                m_idx_vals[j] = val;
            }

            for (unsigned i = start; i < end-1; i++) {
                m_idx_lits.push_back (m_ari_u.mk_lt (m_idx_reprs.get (i),
                                                     m_idx_reprs.get (i+1)));
            }
        }

        void mk_result (expr_ref& fml) {
            // conjoin idx lits
            expr_ref_vector lits (m);
            lits.append (m_idx_lits);
            lits.push_back (fml);
            fml = m.mk_and (lits.size (), lits.c_ptr ());

            // substitute for sel terms
            m_sub (fml);

            TRACE ("qe",
                    tout << "after projection of selects:\n";
                    tout << mk_pp (fml, m) << "\n";
                  );
        }

        /**
         * project selects
         * populates idx lits and obtains substitution for sel terms
         */
        bool project (expr_ref& fml) {
            // collect sel terms -- populate the map m_sel_terms
            collect_selects (fml);

            // model based ackermannization
            sel_map::iterator begin = m_sel_terms.begin (),
                              end = m_sel_terms.end ();
            for (sel_map::iterator it = begin; it != end; it++) {
                TRACE ("qe",
                        tout << "ackermann for var: " << mk_pp (it->m_key, m) << "\n";
                      );
                ackermann (*(it->m_value));
            }

            TRACE ("qe",
                    tout << "idx lits:\n";
                    for (unsigned i = 0; i < m_idx_lits.size (); i++) {
                        tout << mk_pp (m_idx_lits.get (i), m) << "\n";
                    }
                  );

            return true;
        }

    public:

        array_project_selects_util (ast_manager& m):
            m (m),
            m_arr_u (m),
            m_ari_u (m),
            m_idx_reprs (m),
            m_idx_vals (m),
            m_sel_consts (m),
            m_idx_lits (m),
            m_mev (m),
            m_sub (m)
        {}

        void operator () (model& mdl, app_ref_vector& arr_vars, expr_ref& fml, app_ref_vector& aux_vars) {
            reset ();
            M = &mdl;

            // mark vars to eliminate
            for (unsigned i = 0; i < arr_vars.size (); i++) {
                m_arr_test.mark (arr_vars.get (i), true);
            }

            // alloc empty map from array var to sel terms over it
            for (unsigned i = 0; i < arr_vars.size (); i++) {
                ptr_vector<app>* lst = alloc (ptr_vector<app>);
                m_sel_terms.insert (arr_vars.get (i), lst);
            }

            // assume all arr_vars are of array sort
            // and they only appear in select terms
            if (project (fml)) {
                mk_result (fml);
                aux_vars.append (m_sel_consts);
                arr_vars.reset ();
            }
            else {
                IF_VERBOSE(2, verbose_stream() << "can't project arrays:" << "\n";);
                TRACE ("qe", tout << "Failed to project arrays\n";);
            }

            // dealloc
            sel_map::iterator begin = m_sel_terms.begin (),
                              end = m_sel_terms.end ();
            for (sel_map::iterator it = begin; it != end; it++) {
                dealloc (it->m_value);
            }
            m_sel_terms.reset ();
        }
    };

    expr_ref arith_project(model& mdl, app_ref_vector& vars, expr_ref_vector const& lits) {
        ast_manager& m = vars.get_manager();
        arith_project_util ap(m);
        return ap(mdl, vars, lits);
    }

    void arith_project(model& mdl, app_ref_vector& vars, expr_ref& fml) {
        ast_manager& m = vars.get_manager();
        arith_project_util ap(m);
        atom_set pos_lits, neg_lits;
        is_relevant_default is_relevant;
        mk_atom_default mk_atom;
        get_nnf (fml, is_relevant, mk_atom, pos_lits, neg_lits);
        ap(mdl, vars, fml);
    }

    void arith_project(model& mdl, app_ref_vector& vars, expr_ref& fml, expr_map& map) {
        ast_manager& m = vars.get_manager();
        arith_project_util ap(m);
        atom_set pos_lits, neg_lits;
        is_relevant_default is_relevant;
        mk_atom_default mk_atom;
        get_nnf (fml, is_relevant, mk_atom, pos_lits, neg_lits);
        ap(mdl, vars, fml, map);
    }

    void array_project_eqs (model& mdl, app_ref_vector& arr_vars, expr_ref& fml, app_ref_vector& aux_vars) {
        ast_manager& m = arr_vars.get_manager ();
        array_project_eqs_util ap (m);
        ap (mdl, arr_vars, fml, aux_vars);
    }

    void reduce_array_selects (model& mdl, app_ref_vector const& arr_vars, expr_ref& fml, bool reduce_all_selects) {
        ast_manager& m = arr_vars.get_manager ();
        array_select_reducer ap (m);
        ap (mdl, arr_vars, fml, reduce_all_selects);
    }

    void reduce_array_selects (model& mdl, expr_ref& fml) {
        ast_manager& m = fml.get_manager ();
        app_ref_vector _tmp (m);
        reduce_array_selects (mdl, _tmp, fml, true);
    }

    void array_project_selects (model& mdl, app_ref_vector& arr_vars, expr_ref& fml, app_ref_vector& aux_vars) {
        ast_manager& m = arr_vars.get_manager ();
        array_project_selects_util ap (m);
        ap (mdl, arr_vars, fml, aux_vars);
    }

    void array_project (model& mdl, app_ref_vector& arr_vars, expr_ref& fml, app_ref_vector& aux_vars, bool reduce_all_selects) {
        // 1. project array equalities
        array_project_eqs (mdl, arr_vars, fml, aux_vars);
        TRACE ("qe",
                ast_manager& m = fml.get_manager ();
                tout << "Projected array eqs:\n" << mk_pp (fml, m) << "\n";
                tout << "Remaining array vars:\n";
                for (unsigned i = 0; i < arr_vars.size (); i++) {
                    tout << mk_pp (arr_vars.get (i), m) << "\n";
                }
                tout << "Aux vars:\n";
                for (unsigned i = 0; i < aux_vars.size (); i++) {
                    tout << mk_pp (aux_vars.get (i), m) << "\n";
                }
              );

        // 2. reduce selects
        if (reduce_all_selects) {
            reduce_array_selects (mdl, fml);
        }
        else {
            reduce_array_selects (mdl, arr_vars, fml);
        }
        TRACE ("qe",
                ast_manager& m = fml.get_manager ();
                tout << "Reduced selects:\n" << mk_pp (fml, m) << "\n";
              );

        // 3. project selects using model based ackermannization
        array_project_selects (mdl, arr_vars, fml, aux_vars);
        TRACE ("qe",
                ast_manager& m = fml.get_manager ();
                tout << "Projected array selects:\n" << mk_pp (fml, m) << "\n";
                tout << "All aux vars:\n";
                for (unsigned i = 0; i < aux_vars.size (); i++) {
                    tout << mk_pp (aux_vars.get (i), m) << "\n";
                }
              );
    }

}
