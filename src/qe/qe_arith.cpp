/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qe_arith.cpp

Abstract:

    Simple projection function for real arithmetic based on Loos-W.

Author:

    Nikolaj Bjorner (nbjorner) 2013-09-12

Revision History:



--*/

#include "qe_arith.h"
#include "qe_mbp.h"
#include "ast_util.h"
#include "arith_decl_plugin.h"
#include "ast_pp.h"
#include "th_rewriter.h"
#include "expr_functors.h"
#include "model_v2_pp.h"
#include "expr_safe_replace.h"
#include "model_based_opt.h"

namespace qe {

    bool is_divides(arith_util& a, expr* e1, expr* e2, rational& k, expr_ref& p) {  
        expr* t1, *t2;
        if (a.is_mod(e2, t1, t2) && 
            a.is_numeral(e1, k) && 
            k.is_zero() &&
            a.is_numeral(t2, k)) {
            p = t1;
            return true;
        }
        return false;
    }

    bool is_divides(arith_util& a, expr* e, rational& k, expr_ref& t) {
        expr* e1, *e2;
        if (!a.get_manager().is_eq(e, e1, e2)) {
            return false;
        }
        return is_divides(a, e1, e2, k, t) || is_divides(a, e2, e1, k, t);
    }
    
    struct arith_project_plugin::imp {

        ast_manager&      m;
        arith_util        a;
        th_rewriter       m_rw;
        expr_ref_vector   m_ineq_terms;
        vector<rational>  m_ineq_coeffs;
        svector<opt::ineq_type>  m_ineq_types;
        expr_ref_vector   m_div_terms;
        vector<rational>  m_div_divisors, m_div_coeffs;
        expr_ref_vector   m_new_lits;
        rational m_delta, m_u;
        scoped_ptr<contains_app> m_var;
        unsigned m_num_pos, m_num_neg;
        bool m_pos_is_unit, m_neg_is_unit;

        sort* var_sort() const { return m.get_sort(m_var->x()); }

        bool is_int() const { return a.is_int(m_var->x()); }

        void display(std::ostream& out) const {
            for (unsigned i = 0; i < num_ineqs(); ++i) {
                display_ineq(out, i);
            }
            for (unsigned i = 0; i < num_divs(); ++i) {
                display_div(out, i);
            }            
        }

        void insert_mul(expr* x, rational const& v, obj_map<expr, rational>& ts) {
            rational w;
            if (ts.find(x, w)) {
                ts.insert(x, w + v);
            }
            else {
                TRACE("qe", tout << "Adding variable " << mk_pp(x, m) << "\n";);
                ts.insert(x, v); 
            }
        }

        //
        // extract linear inequalities from literal 'lit' into the model-based optimization manager 'mbo'.
        // It uses the current model to choose values for conditionals and it primes mbo with the current
        // interpretation of sub-expressions that are treated as variables for mbo.
        // 
        void linearize(opt::model_based_opt& mbo, model& model, expr* lit, obj_map<expr, unsigned>& tids) {
            obj_map<expr, rational> ts;
            rational c(0), mul(1);
            expr_ref t(m);
            opt::ineq_type ty = opt::t_le;
            expr* e1, *e2;
            bool is_not = m.is_not(lit, lit);
            if (is_not) {
                mul.neg();
            }
            SASSERT(!m.is_not(lit));
            if (a.is_le(lit, e1, e2) || a.is_ge(lit, e2, e1)) {
                if (is_not) mul.neg();
                linearize(mbo, model, mul, e1, c, ts, tids);
                linearize(mbo, model, -mul, e2, c, ts, tids);
                ty = is_not ? opt::t_lt : opt::t_le;
            }
            else if (a.is_lt(lit, e1, e2) || a.is_gt(lit, e2, e1)) {
                if (is_not) mul.neg();
                linearize(mbo, model,  mul, e1, c, ts, tids);
                linearize(mbo, model, -mul, e2, c, ts, tids);
                ty = is_not ? opt::t_le: opt::t_lt;
            }
            else if (m.is_eq(lit, e1, e2) && !is_not && is_arith(e1)) {
                linearize(mbo, model,  mul, e1, c, ts, tids);
                linearize(mbo, model, -mul, e2, c, ts, tids);
                ty = opt::t_eq;
            }  
            else if (m.is_distinct(lit) && !is_not && is_arith(to_app(lit)->get_arg(0))) {
                UNREACHABLE();
            }
            else if (m.is_distinct(lit) && is_not && is_arith(to_app(lit)->get_arg(0))) {
                UNREACHABLE();
            }
            else if (m.is_eq(lit, e1, e2) && is_not && is_arith(e1)) {
                UNREACHABLE();
            }            
            else {
                TRACE("qe", tout << "Skipping " << mk_pp(lit, m) << "\n";);
                return;
            }
#if 0
            TBD for integers
            if (ty == opt::t_lt && false) {
                c += rational(1);
                ty = opt::t_le;
            }            
#endif
            vars coeffs;
            extract_coefficients(mbo, model, ts, tids, coeffs);
            mbo.add_constraint(coeffs, c, ty);
        }

        //
        // convert linear arithmetic term into an inequality for mbo.
        // 
        void linearize(opt::model_based_opt& mbo, model& model, rational const& mul, expr* t, rational& c, 
                       obj_map<expr, rational>& ts, obj_map<expr, unsigned>& tids) {
            expr* t1, *t2, *t3;
            rational mul1;
            expr_ref val(m);
            if (a.is_mul(t, t1, t2) && is_numeral(model, t1, mul1)) {
                linearize(mbo, model, mul* mul1, t2, c, ts, tids);
            }
            else if (a.is_mul(t, t1, t2) && is_numeral(model, t2, mul1)) {
                linearize(mbo, model, mul* mul1, t1, c, ts, tids);
            }
            else if (a.is_add(t)) {
                app* ap = to_app(t);
                for (unsigned i = 0; i < ap->get_num_args(); ++i) {
                    linearize(mbo, model, mul, ap->get_arg(i), c, ts, tids);
                }
            }
            else if (a.is_sub(t, t1, t2)) {
                linearize(mbo, model, mul, t1, c, ts, tids);
                linearize(mbo, model, -mul, t2, c, ts, tids);
            }
            else if (a.is_uminus(t, t1)) {
                linearize(mbo, model, -mul, t1, c, ts, tids);
            }
            else if (a.is_numeral(t, mul1)) {
                c += mul*mul1;
            }
            else if (m.is_ite(t, t1, t2, t3)) {
                VERIFY(model.eval(t1, val));
                SASSERT(m.is_true(val) || m.is_false(val));
                TRACE("qe", tout << mk_pp(t1, m) << " := " << val << "\n";);
                if (m.is_true(val)) {
                    linearize(mbo, model, mul, t2, c, ts, tids);
                    linearize(mbo, model, t1, tids);
                }
                else {
                    expr_ref not_t1(mk_not(m, t1), m);
                    linearize(mbo, model, mul, t3, c, ts, tids);
                    linearize(mbo, model, not_t1, tids);
                }
            }
            else {
                insert_mul(t, mul, ts);
            }
        }

        //
        // extract linear terms from t into c and ts.
        // 
        void is_linear(model& model, rational const& mul, expr* t, rational& c, expr_ref_vector& ts) {
            expr* t1, *t2, *t3;
            rational mul1;
            expr_ref val(m);
            if (t == m_var->x()) {
                c += mul;
            }
            else if (a.is_mul(t, t1, t2) && is_numeral(model, t1, mul1)) {
                is_linear(model, mul* mul1, t2, c, ts);
            }
            else if (a.is_mul(t, t1, t2) && is_numeral(model, t2, mul1)) {
                is_linear(model, mul* mul1, t1, c, ts);
            }
            else if (a.is_add(t)) {
                app* ap = to_app(t);
                for (unsigned i = 0; i < ap->get_num_args(); ++i) {
                    is_linear(model, mul, ap->get_arg(i), c, ts);
                }
            }
            else if (a.is_sub(t, t1, t2)) {
                is_linear(model, mul,  t1, c, ts);
                is_linear(model, -mul, t2, c, ts);
            }
            else if (a.is_uminus(t, t1)) {
                is_linear(model, -mul, t1, c, ts);
            }
            else if (a.is_numeral(t, mul1)) {
                ts.push_back(mk_num(mul*mul1));
            }            
            else if (extract_mod(model, t, val)) {
                ts.push_back(mk_mul(mul, val));
            }
            else if (m.is_ite(t, t1, t2, t3)) {                
                VERIFY(model.eval(t1, val));
                SASSERT(m.is_true(val) || m.is_false(val));
                TRACE("qe", tout << mk_pp(t1, m) << " := " << val << "\n";);
                if (m.is_true(val)) {
                    is_linear(model, mul, t2, c, ts); 
                }
                else {
                    is_linear(model, mul, t3, c, ts); 
                }
            }
            else if ((*m_var)(t)) {
                TRACE("qe", tout << "can't project:" << mk_pp(t, m) << "\n";);
                throw cant_project();
            }
            else {
                ts.push_back(mk_mul(mul, t));
            }
        }

        // 
        // extract linear inequalities from literal lit.
        // 
        bool is_linear(model& model, expr* lit, bool& found_eq) {
            rational c(0), mul(1);
            expr_ref t(m);
            opt::ineq_type ty = opt::t_le;
            expr* e1, *e2;
            expr_ref_vector ts(m);            
            bool is_not = m.is_not(lit, lit);
            if (is_not) {
                mul.neg();
            }
            SASSERT(!m.is_not(lit));
            if (a.is_le(lit, e1, e2) || a.is_ge(lit, e2, e1)) {
                is_linear(model,  mul, e1, c, ts);
                is_linear(model, -mul, e2, c, ts);
                ty = is_not? opt::t_lt : opt::t_le;
            }
            else if (a.is_lt(lit, e1, e2) || a.is_gt(lit, e2, e1)) {
                is_linear(model,  mul, e1, c, ts);
                is_linear(model, -mul, e2, c, ts);
                ty = is_not? opt::t_le: opt::t_lt;
            }
            else if (m.is_eq(lit, e1, e2) && !is_not && is_arith(e1)) {
                is_linear(model,  mul, e1, c, ts);
                is_linear(model, -mul, e2, c, ts);
                ty = opt::t_eq;
            }  
            else if (m.is_distinct(lit) && !is_not && is_arith(to_app(lit)->get_arg(0))) {
                expr_ref val(m);
                rational r;
                app* alit = to_app(lit);
                vector<std::pair<expr*,rational> > nums;
                for (unsigned i = 0; i < alit->get_num_args(); ++i) {
                    VERIFY(model.eval(alit->get_arg(i), val) && a.is_numeral(val, r));
                    nums.push_back(std::make_pair(alit->get_arg(i), r));
                }
                std::sort(nums.begin(), nums.end(), compare_second());
                for (unsigned i = 0; i + 1 < nums.size(); ++i) {
                    SASSERT(nums[i].second < nums[i+1].second);
                    c.reset();
                    ts.reset();
                    is_linear(model,  mul, nums[i+1].first, c, ts);
                    is_linear(model, -mul, nums[i].first,   c, ts);  
                    t = add(ts);
                    accumulate_linear(model, c, t, opt::t_lt);
                }
                t = mk_num(0);
                c.reset();
                return true;
            }
            else if (m.is_distinct(lit) && is_not && is_arith(to_app(lit)->get_arg(0))) {
                expr_ref eq = project_plugin::pick_equality(m, model, to_app(lit)->get_arg(0));
                return is_linear(model, eq, found_eq);
            }
            else if (m.is_eq(lit, e1, e2) && is_not && is_arith(e1)) {
                expr_ref val1(m), val2(m);
                rational r1, r2;
                VERIFY(model.eval(e1, val1) && a.is_numeral(val1, r1));
                VERIFY(model.eval(e2, val2) && a.is_numeral(val2, r2));
                SASSERT(r1 != r2);
                if (r1 < r2) {
                    std::swap(e1, e2);
                }                
                ty = opt::t_lt;
                is_linear(model,  mul, e1, c, ts);
                is_linear(model, -mul, e2, c, ts);    
            }
            else {
                TRACE("qe", tout << "can't project:" << mk_pp(lit, m) << "\n";);
                throw cant_project();
            }
            if (ty == opt::t_lt && is_int()) {
                ts.push_back(mk_num(1));
                ty = opt::t_le;
            }
            t = add(ts);
            if (ty == opt::t_eq && c.is_neg()) {
                t = mk_uminus(t);
                c.neg();
            }
            if (ty == opt::t_eq && c > rational(1)) {
                m_ineq_coeffs.push_back(-c);
                m_ineq_terms.push_back(mk_uminus(t));
                m_ineq_types.push_back(opt::t_le);
                m_num_neg++;
                ty = opt::t_le;
            }
            accumulate_linear(model, c, t, ty);
            found_eq = !c.is_zero() && ty == opt::t_eq;
            return true;
        }

        bool is_numeral(model& model, expr* t, rational& r) {
            expr* t1, *t2, *t3;
            rational r1, r2;
            expr_ref val(m);
            if (a.is_numeral(t, r)) return true;

            if (a.is_uminus(t, t1) && is_numeral(model, t1, r)) {
                r.neg();
                return true;
            }         
            else if (a.is_mul(t, t1, t2) && is_numeral(model, t1, r1) && is_numeral(model, t2, r2)) {
                r = r1*r2;
                return true;
            }
            else if (a.is_add(t)) {
                app* ap = to_app(t);
                r = rational(1);
                for (unsigned i = 0; i < ap->get_num_args(); ++i) {
                    if (!is_numeral(model, ap->get_arg(i), r1)) return false;
                    r *= r1;
                }
                return true;
            }
            else if (m.is_ite(t, t1, t2, t3)) {
                VERIFY (model.eval(t1, val));
                if (m.is_true(val)) {
                    return is_numeral(model, t1, r);
                }
                else {
                    return is_numeral(model, t2, r);
                }
            }
            else if (a.is_sub(t, t1, t2) && is_numeral(model, t1, r1) && is_numeral(model, t2, r2)) {
                r = r1 - r2;
                return true;
            }
            
            return false;
        }

        struct compare_second {
            bool operator()(std::pair<expr*, rational> const& a, 
                            std::pair<expr*, rational> const& b) const {
                return a.second < b.second;
            }
        };

        void accumulate_linear(model& model, rational const& c, expr_ref& t, opt::ineq_type ty) {
            if (c.is_zero()) {
                switch (ty) {
                case opt::t_eq:
                    t = a.mk_eq(t, mk_num(0));
                    break;
                case opt::t_lt:
                    t = a.mk_lt(t, mk_num(0));
                    break;
                case opt::t_le:
                    t = a.mk_le(t, mk_num(0));
                    break;
                }
                add_lit(model, m_new_lits, t);
            }
            else {
                m_ineq_coeffs.push_back(c);
                m_ineq_terms.push_back(t);
                m_ineq_types.push_back(ty);
                if (ty == opt::t_eq) {
                    // skip
                }
                else if (c.is_pos()) {
                    ++m_num_pos;
                    m_pos_is_unit &= c.is_one();
                }
                else {
                    ++m_num_neg;
                    m_neg_is_unit &= c.is_minus_one();
                }            
            }        
        }

        bool is_arith(expr* e) {
            return a.is_int(e) || a.is_real(e);
        }

        expr_ref add(expr_ref_vector const& ts) {
            switch (ts.size()) {
            case 0:
                return mk_num(0);
            case 1:
                return expr_ref(ts[0], m);
            default:
                return expr_ref(a.mk_add(ts.size(), ts.c_ptr()), m);
            }
        }


        // e is of the form  (ax + t) mod k
        bool is_mod(model& model, expr* e, rational& k, expr_ref& t, rational& c) {
            expr* t1, *t2;
            expr_ref_vector ts(m);
            if (a.is_mod(e, t1, t2) &&
                a.is_numeral(t2, k) &&
                (*m_var)(t1)) {
                c.reset();
                rational mul(1);
                is_linear(model, mul, t1, c, ts);
                t = add(ts);
                return true;
            }
            return false;
        }

        bool extract_mod(model& model, expr* e, expr_ref& val) {
            rational c, k;
            expr_ref t(m);
            if (is_mod(model, e, k, t, c)) {                
                VERIFY (model.eval(e, val));
                SASSERT (a.is_numeral(val));
                TRACE("qe", tout << "extract: " << mk_pp(e, m) << " evals: " << val << " c: " << c << " t: " << t << "\n";);
                if (!c.is_zero()) {
                    t = mk_sub(t, val);
                    m_div_terms.push_back(t);
                    m_div_divisors.push_back(k);
                    m_div_coeffs.push_back(c);
                }
                else {
                    t = m.mk_eq(a.mk_mod(t, mk_num(k)), val);
                    add_lit(model, m_new_lits, t);
                }
                return true;
            }
            return false;
        }

        bool lit_is_true(model& model, expr* e) {
            expr_ref val(m);
            VERIFY(model.eval(e, val));
            CTRACE("qe", !m.is_true(val), tout << "eval: " << mk_pp(e, m) << " " << val << "\n";);
            return m.is_true(val);
        }

        expr_ref mk_num(unsigned n) {
            rational r(n);
            return mk_num(r);
        }

        expr_ref mk_num(rational const& r) const {
            return expr_ref(a.mk_numeral(r, var_sort()), m);
        }

        expr_ref mk_divides(rational const& k, expr* t) {            
            return expr_ref(m.mk_eq(a.mk_mod(t, mk_num(abs(k))), mk_num(0)), m);
        }

        void reset() {
            reset_ineqs();
            reset_divs();
            m_delta = rational(1);
            m_u     = rational(0);
            m_new_lits.reset();
        }

        void reset_divs() {
            m_div_terms.reset();
            m_div_coeffs.reset();
            m_div_divisors.reset();
        }

        void reset_ineqs() {
            m_ineq_terms.reset();
            m_ineq_coeffs.reset();
            m_ineq_types.reset();
        }

        expr* ineq_term(unsigned i) const { return m_ineq_terms[i]; }
        rational const& ineq_coeff(unsigned i) const { return m_ineq_coeffs[i]; }
        opt::ineq_type ineq_ty(unsigned i) const { return m_ineq_types[i]; }
        app_ref mk_ineq_pred(unsigned i) { 
            app_ref result(m);
            result = to_app(mk_add(mk_mul(ineq_coeff(i), m_var->x()), ineq_term(i)));
            switch (ineq_ty(i)) {
            case opt::t_lt:
                result = a.mk_lt(result, mk_num(0));
                break;
            case opt::t_le:
                result = a.mk_le(result, mk_num(0));
                break;
            case opt::t_eq:
                result = m.mk_eq(result, mk_num(0));
                break;
            }
            return result;
        }
        void display_ineq(std::ostream& out, unsigned i) const {
            out << mk_pp(ineq_term(i), m) << " " << ineq_coeff(i) << "*" << mk_pp(m_var->x(), m);
            switch (ineq_ty(i)) {
            case opt::t_eq: out <<  " = 0\n"; break;
            case opt::t_le: out << " <= 0\n"; break;
            case opt::t_lt: out <<  " < 0\n"; break;
            }
        }
        unsigned num_ineqs() const { return m_ineq_terms.size(); }
        expr* div_term(unsigned i) const { return m_div_terms[i]; }
        rational const& div_coeff(unsigned i) const { return m_div_coeffs[i]; }
        rational const& div_divisor(unsigned i) const { return m_div_divisors[i]; }
        void display_div(std::ostream& out, unsigned i) const {
            out << div_divisor(i) << " | ( " << mk_pp(div_term(i), m) << " " << div_coeff(i) << "*" 
                << mk_pp(m_var->x(), m) << ")\n";
        }
        unsigned num_divs() const { return m_div_terms.size(); }

        void project(model& model, expr_ref_vector& lits) {
            TRACE("qe", 
                  tout << "project: " << mk_pp(m_var->x(), m) << "\n";
                  tout << lits;
                  model_v2_pp(tout, model); );

            m_num_pos = 0; m_num_neg = 0;
            m_pos_is_unit = true; m_neg_is_unit = true;
            unsigned eq_index = 0;
            reset();
            bool found_eq = false;
            for (unsigned i = 0; i < lits.size(); ++i) {
                bool found_eq0 = false;
                expr* e = lits[i].get();
                if (!(*m_var)(e)) {
                    m_new_lits.push_back(e);                    
                }
                else if (!is_linear(model, e, found_eq0)) {
                    TRACE("qe", tout << "can't project:" << mk_pp(e, m) << "\n";);
                    throw cant_project();
                }
                if (found_eq0 && !found_eq) {
                    found_eq = true;
                    eq_index = num_ineqs()-1;
                }
            }
            TRACE("qe", display(tout << mk_pp(m_var->x(), m) << ":\n");
                  tout << "found eq: " << found_eq << " @ " << eq_index << "\n";
                  tout << "num pos: " << m_num_pos << " num neg: " << m_num_neg << " num divs " << num_divs() << "\n";
                  );
            lits.reset();
            lits.append(m_new_lits);
            if (found_eq) {
                apply_equality(model, eq_index, lits);
                return;
            }
            if (num_divs() == 0 && (m_num_pos == 0 || m_num_neg == 0)) {
                return;
            }
            if (num_divs() > 0) {
                apply_divides(model, lits);
                TRACE("qe", display(tout << "after division " << mk_pp(m_var->x(), m) << "\n"););
            }
            if (m_num_pos == 0 || m_num_neg == 0) {
                return;
            }
            if ((m_num_pos <= 2 || m_num_neg <= 2) &&
                (m_num_pos == 1 || m_num_neg == 1 || (m_num_pos <= 3 && m_num_neg <= 3)) && 
                (!is_int() || m_pos_is_unit || m_neg_is_unit)) {
                
                unsigned index1 = num_ineqs();
                unsigned index2 = num_ineqs();
                bool is_pos = m_num_pos <= m_num_neg;
                for (unsigned i = 0; i < num_ineqs(); ++i) {
                    if (ineq_coeff(i).is_pos() == is_pos) {
                        if (index1 == num_ineqs()) {
                            index1 = i;
                        }
                        else {
                            SASSERT(index2 == num_ineqs());
                            index2 = i;
                        }
                    }
                }
                for (unsigned i = 0; i < num_ineqs(); ++i) {
                    if (ineq_coeff(i).is_pos() != is_pos) {
                        SASSERT(index1 != num_ineqs());
                        mk_lt(model, lits, i, index1);
                        if (index2 != num_ineqs()) {
                            mk_lt(model, lits, i, index2);
                        }
                    }
                }
            }
            else {
                expr_ref t(m);
                bool use_pos = m_num_pos < m_num_neg;
                unsigned max_t = find_max(model, use_pos);
                
                for (unsigned i = 0; i < num_ineqs(); ++i) {
                    if (i != max_t) {
                        if (ineq_coeff(i).is_pos() == use_pos) {
                            t = mk_le(i, max_t);
                            add_lit(model, lits, t);
                        }
                        else {
                            mk_lt(model, lits, i, max_t);
                        }
                    }
                }
            }
            TRACE("qe", tout << lits;);
        }

        unsigned find_max(model& mdl, bool do_pos) {
            unsigned result;
            bool new_max = true;
            rational max_r, r;
            expr_ref val(m);
            bool is_int = a.is_int(m_var->x());
            for (unsigned i = 0; i < num_ineqs(); ++i) {
                rational const& ac = m_ineq_coeffs[i];
                SASSERT(!is_int || opt::t_le == ineq_ty(i));

                //
                // ac*x + t < 0
                // ac > 0: x + max { t/ac | ac > 0 } < 0   <=> x < - max { t/ac | ac > 0 }
                // ac < 0: x + t/ac > 0 <=> x > max { - t/ac | ac < 0 } = max { t/|ac| | ac < 0 } 
                //
                if (ac.is_pos() == do_pos) {
                    VERIFY(mdl.eval(ineq_term(i), val));
                    VERIFY(a.is_numeral(val, r));
                    r /= abs(ac);
                    new_max =
                        new_max || 
                        (r > max_r) || 
                        (r == max_r && opt::t_lt == ineq_ty(i)) ||
                        (r == max_r && is_int && ac.is_one());
                    TRACE("qe", tout << "max: "  << mk_pp(ineq_term(i), m) << "/" << abs(ac) << " := " << r << " " 
                          << (new_max?"":"not ") << "new max\n";);
                    if (new_max) { 
                        result = i;
                        max_r  = r;
                    }
                    new_max = false;
                }
            }
            SASSERT(!new_max);
            return result;
        }

        // ax + t <= 0
        // bx + s <= 0
        // a and b have different signs.
        // Infer: a|b|x + |b|t + |a|bx + |a|s <= 0
        // e.g.   |b|t + |a|s <= 0
        void mk_lt(model& model, expr_ref_vector& lits, unsigned i, unsigned j) {
            rational const& ac = ineq_coeff(i);
            rational const& bc = ineq_coeff(j);
            SASSERT(ac.is_pos() != bc.is_pos());
            SASSERT(ac.is_neg() != bc.is_neg());
            
            TRACE("qe", display_ineq(tout, i); display_ineq(tout, j););

            if (is_int() && !abs(ac).is_one() && !abs(bc).is_one()) {
                return mk_int_lt(model, lits, i, j);
            }
            expr* t = ineq_term(i);
            expr* s = ineq_term(j);
            expr_ref bt = mk_mul(abs(bc), t);
            expr_ref as = mk_mul(abs(ac), s);
            expr_ref ts = mk_add(bt, as);
            expr_ref  z = mk_num(0);
            expr_ref  fml(m);
            if (opt::t_lt == ineq_ty(i) || opt::t_lt == ineq_ty(j)) {
                fml = a.mk_lt(ts, z);
            }
            else {
                fml = a.mk_le(ts, z);
            }
            add_lit(model, lits, fml);
        }

        void mk_int_lt(model& model, expr_ref_vector& lits, unsigned i, unsigned j) {
            TRACE("qe", display_ineq(tout, i); display_ineq(tout, j););

            expr* t = ineq_term(i);
            expr* s = ineq_term(j);
            rational ac = ineq_coeff(i);
            rational bc = ineq_coeff(j);
            expr_ref tmp(m);
            SASSERT(opt::t_le == ineq_ty(i) && opt::t_le == ineq_ty(j));
            SASSERT(ac.is_pos() == bc.is_neg());
            rational abs_a = abs(ac);
            rational abs_b = abs(bc);
            expr_ref as(mk_mul(abs_a, s), m);
            expr_ref bt(mk_mul(abs_b, t), m);
            
            rational slack = (abs_a - rational(1))*(abs_b-rational(1));
            rational sval, tval;
            VERIFY (model.eval(ineq_term(i), tmp) && a.is_numeral(tmp, tval));
            VERIFY (model.eval(ineq_term(j), tmp) && a.is_numeral(tmp, sval));
            bool use_case1 = ac*sval + bc*tval + slack <= rational(0);
            if (use_case1) {
                expr_ref_vector ts(m);
                ts.push_back(as);
                ts.push_back(bt);
                ts.push_back(mk_num(-slack));
                tmp = a.mk_le(add(ts), mk_num(0));
                add_lit(model, lits, tmp);
                return;
            }

            if (abs_a < abs_b) {
                std::swap(abs_a, abs_b);
                std::swap(ac, bc);
                std::swap(s, t);
                std::swap(as, bt);
                std::swap(sval, tval);
            }
            SASSERT(abs_a >= abs_b);                
            
            // create finite disjunction for |b|.                                
            //    exists x, z in [0 .. |b|-2] . b*x + s + z = 0 && ax + t <= 0 && bx + s <= 0
            // <=> 
            //    exists x, z in [0 .. |b|-2] . b*x = -z - s && ax + t <= 0 && bx + s <= 0
            // <=>
            //    exists x, z in [0 .. |b|-2] . b*x = -z - s && a|b|x + |b|t <= 0 && bx + s <= 0
            // <=>
            //    exists x, z in [0 .. |b|-2] . b*x = -z - s && a|b|x + |b|t <= 0 && -z - s + s <= 0
            // <=>
            //    exists x, z in [0 .. |b|-2] . b*x = -z - s && a|b|x + |b|t <= 0 && -z <= 0
            // <=>
            //    exists x, z in [0 .. |b|-2] . b*x = -z - s && a|b|x + |b|t <= 0
            // <=>
            //    exists x, z in [0 .. |b|-2] . b*x = -z - s && a*n_sign(b)(s + z) + |b|t <= 0
            // <=>
            //    exists z in [0 .. |b|-2] . |b| | (z + s) && a*n_sign(b)(s + z) + |b|t <= 0
            //
              
            rational z = mod(sval, abs_b);
            if (!z.is_zero()) z = abs_b - z;
            expr_ref s_plus_z(mk_add(z, s), m);
            
            tmp = mk_divides(abs_b, s_plus_z);
            add_lit(model, lits, tmp);
            tmp = a.mk_le(mk_add(mk_mul(ac*n_sign(bc), s_plus_z),
                                 mk_mul(abs_b, t)), mk_num(0));
            add_lit(model, lits, tmp);
        }

        rational n_sign(rational const& b) {
            return rational(b.is_pos()?-1:1);
        }

        // ax + t <= 0
        // bx + s <= 0
        // a and b have same signs.
        // encode:
        // t/|a| <= s/|b|
        // e.g.   |b|t <= |a|s
        expr_ref mk_le(unsigned i, unsigned j) {
            rational const& ac = ineq_coeff(i);
            rational const& bc = ineq_coeff(j);
            SASSERT(ac.is_pos() == bc.is_pos());
            SASSERT(ac.is_neg() == bc.is_neg());
            expr* t = ineq_term(i);
            expr* s = ineq_term(j);
            expr_ref bt = mk_mul(abs(bc), t);
            expr_ref as = mk_mul(abs(ac), s);
            if (opt::t_lt == ineq_ty(i) && opt::t_le == ineq_ty(j)) {
                return expr_ref(a.mk_lt(bt, as), m);
            }
            else {
                return expr_ref(a.mk_le(bt, as), m);
            }
        }

        expr_ref mk_add(expr* t1, expr* t2) {
            rational r;
            if (a.is_numeral(t1, r) && r.is_zero()) return expr_ref(t2, m);
            if (a.is_numeral(t2, r) && r.is_zero()) return expr_ref(t1, m);
            return expr_ref(a.mk_add(t1, t2), m);
        }
        expr_ref mk_add(rational const& r, expr* e) {
            if (r.is_zero()) return expr_ref(e, m);
            return mk_add(mk_num(r), e);
        }
                                  
        expr_ref mk_mul(rational const& r, expr* t) {
            if (r.is_one()) return expr_ref(t, m);
            return expr_ref(a.mk_mul(mk_num(r), t), m);
        }

        expr_ref mk_sub(expr* t1, expr* t2) {
            rational r1, r2;
            if (a.is_numeral(t2, r2) && r2.is_zero()) return expr_ref(t1, m);
            if (a.is_numeral(t1, r1) && a.is_numeral(t2, r2)) return mk_num(r1 - r2);
            return expr_ref(a.mk_sub(t1, t2), m);
        }

        expr_ref mk_uminus(expr* t) {
            rational r;
            if (a.is_numeral(t, r)) {
                return mk_num(-r);
            }
            return expr_ref(a.mk_uminus(t), m);
        }

        void add_lit(model& model, expr_ref_vector& lits, expr* e) { 
            expr_ref orig(e, m), result(m);
            m_rw(orig, result);            
            TRACE("qe", tout << mk_pp(orig, m) << " -> " << result << "\n";); 
            SASSERT(lit_is_true(model, orig));
            SASSERT(lit_is_true(model, result));
            if (!m.is_true(result)) {
                lits.push_back(result);
            }
        }


        // 3x + t = 0 & 7 | (c*x + s) & ax <= u 
        // 3 | -t  & 21 | (-ct + 3s) & a-t <= 3u

        void apply_equality(model& model, unsigned eq_index, expr_ref_vector& lits) {
            rational c = ineq_coeff(eq_index);
            expr* t = ineq_term(eq_index);
            SASSERT(c.is_pos());
            if (is_int()) {
                add_lit(model, lits, mk_divides(c, ineq_term(eq_index)));
            }
            
            for (unsigned i = 0; i < num_divs(); ++i) {
                add_lit(model, lits, mk_divides(c*div_divisor(i), 
                                                mk_sub(mk_mul(c, div_term(i)), mk_mul(div_coeff(i), t))));
            }
            for (unsigned i = 0; i < num_ineqs(); ++i) {
                if (eq_index != i) {
                    expr_ref lhs(m), val(m);
                    lhs = mk_sub(mk_mul(c, ineq_term(i)), mk_mul(ineq_coeff(i), t));
                    switch (ineq_ty(i)) {
                    case opt::t_lt: lhs = a.mk_lt(lhs, mk_num(0)); break;
                    case opt::t_le: lhs = a.mk_le(lhs, mk_num(0)); break;
                    case opt::t_eq: lhs = m.mk_eq(lhs, mk_num(0)); break;
                    }
                    TRACE("qe", tout << lhs << "\n";);
                    SASSERT (model.eval(lhs, val) && m.is_true(val));
                    add_lit(model, lits, lhs);
                }
            }
        }

        // 
        // compute D and u.
        //
        // D = lcm(d1, d2)
        // u = eval(x) mod D
        // 
        //   d1 | (a1x + t1) & d2 | (a2x + t2)
        // = 
        //   D | (D/d1)(a1x + t1) & D | (D/d2)(a2x + t2)
        // =
        //   D | D1(a1*u + t1) & D | D2(a2*u + t2) & x = D*x' + u & 0 <= u < D
        // =
        //   D | D1(a1*u + t1) & D | D2(a2*u + t2) & x = D*x' + u & 0 <= u < D
        // 
        // x := D*x' + u
        // 
        void apply_divides(model& model, expr_ref_vector& lits) {
            SASSERT(m_delta.is_one());
            unsigned n = num_divs();
            if (n == 0) {
                return;
            }
            for (unsigned i = 0; i < n; ++i) {
                m_delta = lcm(m_delta, div_divisor(i));
            }
            expr_ref val(m);
            rational r;
            VERIFY (model.eval(m_var->x(), val) && a.is_numeral(val, r));
            m_u = mod(r, m_delta);
            SASSERT(m_u < m_delta && rational(0) <= m_u);
            for (unsigned i = 0; i < n; ++i) {
                add_lit(model, lits, mk_divides(div_divisor(i), 
                                         mk_add(mk_num(div_coeff(i) * m_u), div_term(i))));
            }
            reset_divs();
            //
            // update inequalities such that u is added to t and
            // D is multiplied to coefficient of x.
            // the interpretation of the new version of x is (x-u)/D
            //
            // a*x + t <= 0
            // a*(D*x' + u) + t <= 0
            // a*D*x' + a*u + t <= 0
            for (unsigned i = 0; i < num_ineqs(); ++i) {
                if (!m_u.is_zero()) {
                    m_ineq_terms[i] = a.mk_add(ineq_term(i), mk_num(m_ineq_coeffs[i]*m_u));
                }
                m_ineq_coeffs[i] *= m_delta;
            }
            r = (r - m_u) / m_delta;
            SASSERT(r.is_int());
            val = a.mk_numeral(r, true);
            model.register_decl(m_var->x()->get_decl(), val);
            TRACE("qe", model_v2_pp(tout, model););
        }

        imp(ast_manager& m): 
            m(m), a(m), m_rw(m), m_ineq_terms(m), m_div_terms(m), m_new_lits(m) {
            params_ref params;
            params.set_bool("gcd_rouding", true);
            m_rw.updt_params(params);
        }

        ~imp() {
        }

        bool solve(model& model, app_ref_vector& vars, expr_ref_vector& lits) {
            return false;
        }

        bool operator()(model& model, app* v, app_ref_vector& vars, expr_ref_vector& lits) {
            SASSERT(a.is_real(v) || a.is_int(v));
            m_var = alloc(contains_app, m, v);
            try {
                project(model, lits);
            }
            catch (cant_project) {
                TRACE("qe", tout << "can't project:" << mk_pp(v, m) << "\n";);
                return false;
            }
            return true;
        }

        typedef opt::model_based_opt::var var;
        typedef vector<var> vars;
        

        opt::inf_eps maximize(expr_ref_vector const& fmls, model& mdl, app* t, expr_ref& bound) {
            SASSERT(a.is_real(t));
            opt::model_based_opt mbo;
            opt::inf_eps value;
            obj_map<expr, rational> ts;
            obj_map<expr, unsigned> tids;

            // extract objective function.
            vars coeffs;
            rational c(0), mul(1);
            linearize(mbo, mdl, mul, t, c, ts, tids);
            extract_coefficients(mbo, mdl, ts, tids, coeffs);
            mbo.set_objective(coeffs, c);

            // extract linear constraints
            for (unsigned i = 0; i < fmls.size(); ++i) {
                linearize(mbo, mdl, fmls[i], tids);
            }
            
            // find optimal value
            value = mbo.maximize();

            expr_ref val(a.mk_numeral(value.get_rational(), false), m);
            if (!value.is_finite()) {
                bound = m.mk_false();
                return value;
            }

            // update model to use new values that satisfy optimality
            ptr_vector<expr> vars;
            obj_map<expr, unsigned>::iterator it = tids.begin(), end = tids.end();
            for (; it != end; ++it) {
                expr* e = it->m_key;
                if (is_uninterp_const(e)) {
                    unsigned id = it->m_value;
                    func_decl* f = to_app(e)->get_decl();
                    expr_ref val(a.mk_numeral(mbo.get_value(id), false), m);
                    mdl.register_decl(f, val);
                }
                else {
                    TRACE("qe", tout << "omitting model update for non-uninterpreted constant " << mk_pp(e, m) << "\n";);
                }
            }

            // update the predicate 'bound' which forces larger values.
            if (value.get_infinitesimal().is_neg()) {
                bound = a.mk_le(val, t);
            }
            else {
                bound = a.mk_lt(val, t);
            }            
            return value;
        }

        void extract_coefficients(opt::model_based_opt& mbo, model& model, obj_map<expr, rational> const& ts, obj_map<expr, unsigned>& tids, vars& coeffs) {
            coeffs.reset();
            obj_map<expr, rational>::iterator it = ts.begin(), end = ts.end();
            for (; it != end; ++it) {
                unsigned id;
                if (!tids.find(it->m_key, id)) {
                    rational r;
                    expr_ref val(m);
                    if (model.eval(it->m_key, val) && a.is_numeral(val, r)) {
                        id = mbo.add_var(r);
                    }
                    else {
                        TRACE("qe", tout << "extraction of coefficients cancelled\n";);
                        return;
                    }
                    tids.insert(it->m_key, id);
                }
                coeffs.push_back(var(id, it->m_value));                
            }
        }

    };

    arith_project_plugin::arith_project_plugin(ast_manager& m) {
        m_imp = alloc(imp, m);
    }

    arith_project_plugin::~arith_project_plugin() {
        dealloc(m_imp);
    }

    bool arith_project_plugin::operator()(model& model, app* var, app_ref_vector& vars, expr_ref_vector& lits) {
        return (*m_imp)(model, var, vars, lits);
    }

    bool arith_project_plugin::solve(model& model, app_ref_vector& vars, expr_ref_vector& lits) {
        return m_imp->solve(model, vars, lits);
    }

    family_id arith_project_plugin::get_family_id() {
        return m_imp->a.get_family_id();
    }

    opt::inf_eps arith_project_plugin::maximize(expr_ref_vector const& fmls, model& mdl, app* t, expr_ref& bound) {
        return m_imp->maximize(fmls, mdl, t, bound);
    }

    bool arith_project(model& model, app* var, expr_ref_vector& lits) {
        ast_manager& m = lits.get_manager();
        arith_project_plugin ap(m);
        app_ref_vector vars(m);
        return ap(model, var, vars, lits);
    }
}
