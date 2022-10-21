/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    arith_proof_checker.h

Abstract:

    Plugin for checking arithmetic lemmas

Author:

    Nikolaj Bjorner (nbjorner) 2022-08-28

Notes:

The module assumes a limited repertoire of arithmetic proof rules.

- farkas - inequalities, equalities and disequalities with coefficients
- implied-eq - last literal is a disequality. The literals before imply the complementary equality.
- bound - last literal is a bound. It is implied by prior literals.

--*/
#pragma once

#include "util/obj_pair_set.h"
#include "ast/ast_trail.h"
#include "ast/ast_util.h"
#include "ast/arith_decl_plugin.h"
#include "sat/smt/euf_proof_checker.h"
#include <iostream>


namespace arith {

    class theory_checker : public euf::theory_checker_plugin {
        struct row {
            obj_map<expr, rational> m_coeffs;
            rational m_coeff;
            void reset() {
                m_coeffs.reset();
                m_coeff = 0;
            }
        };
       
        ast_manager& m;
        arith_util   a;
        vector<std::pair<rational, expr*>> m_todo;
        bool         m_strict = false;
        row          m_ineq;
        row          m_conseq;
        vector<row>  m_eqs;
        symbol       m_farkas;
        symbol       m_implied_eq;
        symbol       m_bound;
        
        void add(row& r, expr* v, rational const& coeff) {
            rational coeff1;
            if (coeff.is_zero())
                return;
            if (r.m_coeffs.find(v, coeff1)) {
                coeff1 += coeff;
                if (coeff1.is_zero())
                    r.m_coeffs.erase(v);
                else
                    r.m_coeffs[v] = coeff1;
            }
            else
                r.m_coeffs.insert(v, coeff);
        }
        
        void mul(row& r, rational const& coeff) {
            if (coeff == 1)
                return;
            for (auto & [v, c] : r.m_coeffs)
                c *= coeff;
            r.m_coeff *= coeff;
        }
        
        // dst <- dst + mul*src
        void add(row& dst, row const& src, rational const& mul) {
            for (auto const& [v, c] : src.m_coeffs)
                add(dst, v, c*mul);
            dst.m_coeff += mul*src.m_coeff;
        }
        
        // dst <- X*dst + Y*src
        // where
        // X = lcm(a,b)/b, Y = -lcm(a,b)/a  if v is integer
        // X = 1/b, Y = -1/a                if v is real
        //
        void resolve(expr* v, row& dst, rational const& A, row const& src) {
            rational B, x, y;
            if (!dst.m_coeffs.find(v, B))
                return;
            if (a.is_int(v)) {
                rational lc = lcm(abs(A), abs(B));
                x =  lc / abs(B);
                y =  lc / abs(A);
            }
            else {
                x = rational(1)  / abs(B);
                y = rational(1)  / abs(A);
            }
            if (A < 0 && B < 0)
                y.neg();
            if (A > 0 && B > 0)
                y.neg();
            mul(dst, x);
            add(dst, src, y);
        }

        void cut(row& r) {
            if (r.m_coeffs.empty())
                return;
            auto const& [v, coeff] = *r.m_coeffs.begin();
            if (!a.is_int(v))
                return;
            rational lc = denominator(r.m_coeff);
            for (auto const& [v, coeff] : r.m_coeffs)
                lc = lcm(lc, denominator(coeff));
            if (lc != 1) {
                r.m_coeff *= lc;
                for (auto & [v, coeff] : r.m_coeffs)
                    coeff *= lc;
            }
            rational g(0);
            for (auto const& [v, coeff] : r.m_coeffs)
                g = gcd(coeff, g);
            if (g == 1)
                return;
            rational m = mod(r.m_coeff, g);
            if (m == 0)
                return;
            r.m_coeff += g - m;
        }
        
        /**
         * \brief populate m_coeffs, m_coeff based on mul*e 
         */
        void linearize(row& r, rational const& mul, expr* e) {
            SASSERT(m_todo.empty());
            m_todo.push_back({ mul, e });
            rational coeff1;
            expr* e1, *e2;
            for (unsigned i = 0; i < m_todo.size(); ++i) {
                auto [coeff, e] = m_todo[i];
                if (a.is_mul(e, e1, e2) && is_numeral(e1, coeff1))
                    m_todo.push_back({coeff*coeff1, e2});
                else if (a.is_mul(e, e1, e2) && is_numeral(e2, coeff1))
                    m_todo.push_back({ coeff * coeff1, e1 });
                else if (a.is_add(e))
                    for (expr* arg : *to_app(e))
                        m_todo.push_back({coeff, arg});
                else if (a.is_uminus(e, e1))
                    m_todo.push_back({-coeff, e1});
                else if (a.is_sub(e, e1, e2)) {
                    m_todo.push_back({coeff, e1});
                    m_todo.push_back({-coeff, e2});                
                }
                else if (is_numeral(e, coeff1)) 
                    r.m_coeff += coeff*coeff1;
                else
                    add(r, e, coeff);
            }
            m_todo.reset();
        }

        bool is_numeral(expr* e, rational& n) {
            if (a.is_numeral(e, n))
                return true;
            if (a.is_uminus(e, e) && a.is_numeral(e, n))
                return n.neg(), true;
            return false;
        }
        
        bool check_ineq(row& r) {
            if (r.m_coeffs.empty() && r.m_coeff > 0)
                return true;
            if (r.m_coeffs.empty() && m_strict && r.m_coeff == 0)
                return true;
            return false;
        }
        
        // triangulate equalities, substitute results into m_ineq, m_conseq.
        // check consistency of equalities (they may be inconsisent)
        bool reduce_eq() {
            for (unsigned i = 0; i < m_eqs.size(); ++i) {
                auto& r = m_eqs[i];
                if (r.m_coeffs.empty() && r.m_coeff != 0)
                    return false;
                if (r.m_coeffs.empty())
                    continue;
                auto [v, coeff] = *r.m_coeffs.begin();
                for (unsigned j = i + 1; j < m_eqs.size(); ++j)
                    resolve(v, m_eqs[j], coeff, r);
                resolve(v, m_ineq, coeff, r);
                resolve(v, m_conseq, coeff, r);
            }
            return true;
        }
        
        
        bool add_literal(row& r, rational const& coeff, expr* e, bool sign) {
            expr* e1, *e2 = nullptr;
            if ((a.is_le(e, e1, e2) || a.is_ge(e, e2, e1)) && !sign) {
                linearize(r, coeff, e1);
                linearize(r, -coeff, e2);
            }
            else if ((a.is_lt(e, e1, e2) || a.is_gt(e, e2, e1)) && sign) {
                linearize(r, coeff, e2);
                linearize(r, -coeff, e1);
            }
            else if ((a.is_le(e, e1, e2) || a.is_ge(e, e2, e1)) && sign) {
                linearize(r, coeff, e2);
                linearize(r, -coeff, e1);
                if (a.is_int(e1))
                    r.m_coeff += coeff;
                else
                    m_strict = true;
            }
            else if ((a.is_lt(e, e1, e2) || a.is_gt(e, e2, e1)) && !sign) {
                linearize(r, coeff, e1);
                linearize(r, -coeff, e2);
                if (a.is_int(e1))
                    r.m_coeff += coeff;
                else
                    m_strict = true;
            }
            else
                return false;
            // display_row(std::cout << coeff << " * " << (sign?"~":"") << mk_pp(e, m) << "\n", r) << "\n";
            return true;
        }
        
        bool check_farkas() {
            if (check_ineq(m_ineq))
                return true;
            if (!reduce_eq())
                return true;
            if (check_ineq(m_ineq))
                return true;
            IF_VERBOSE(3, display_row(verbose_stream() << "Failed to verify Farkas with reduced row ", m_ineq) << "\n");
            // convert to expression, maybe follows from a cut.
            return false;
        }

        //
        // farkas coefficient is computed for m_conseq 
        // after all inequalities in ineq have been added up
        //
        bool check_bound() {
            if (!reduce_eq())
                return true;
            if (check_ineq(m_conseq))
                return true;
            if (m_ineq.m_coeffs.empty() ||
                m_conseq.m_coeffs.empty())
                return false;
            cut(m_ineq);
            auto const& [v, coeff1] = *m_ineq.m_coeffs.begin();
            rational coeff2;
            if (!m_conseq.m_coeffs.find(v, coeff2))
                return false;
            add(m_conseq, m_ineq, abs(coeff2/coeff1));
            if (check_ineq(m_conseq))
                return true;            
            return false;
        }

        std::ostream& display_row(std::ostream& out, row const& r) {
            bool first = true;
            for (auto const& [v, coeff] : r.m_coeffs) {
                if (!first)
                    out << " + ";
                if (coeff != 1)
                    out << coeff << " * ";
                out << mk_pp(v, m);
                first = false;
            }
            if (r.m_coeff != 0) 
                out << " + " << r.m_coeff;                
            return out;
        }


        void display_eq(std::ostream& out, row const& r) {
            display_row(out, r);
            out << " = 0\n";
        }

        void display_ineq(std::ostream& out, row const& r) {
            display_row(out, r);
            if (m_strict)
                out << " < 0\n";
            else 
                out << " <= 0\n";
        }

        row& fresh(vector<row>& rows) {
            rows.push_back(row());
            return rows.back();
        }
        
    public:
        theory_checker(ast_manager& m): 
            m(m), 
            a(m), 
            m_farkas("farkas"), 
            m_implied_eq("implied-eq"), 
            m_bound("bound") {}

        void reset() {
            m_ineq.reset();
            m_conseq.reset();
            m_eqs.reset();
            m_strict = false;
        }
        
        bool add_ineq(rational const& coeff, expr* e, bool sign) {
            return add_literal(m_ineq, abs(coeff), e, sign);
        }
        
        bool add_conseq(rational const& coeff, expr* e, bool sign) {
            return add_literal(m_conseq, abs(coeff), e, sign);
        }
        
        void add_eq(expr* a, expr* b) {
            row& r = fresh(m_eqs);
            linearize(r, rational(1), a);
            linearize(r, rational(-1), b);
        }
        
        bool check() {
            if (m_conseq.m_coeffs.empty())
                return check_farkas();
            else
                return check_bound();
        }

        std::ostream& display(std::ostream& out) {
            for (auto & r : m_eqs)
                display_eq(out, r);
            display_ineq(out, m_ineq);
            if (!m_conseq.m_coeffs.empty())
                display_ineq(out, m_conseq);
            return out;
        }

        expr_ref_vector clause(app* jst) override {
            expr_ref_vector result(m);
            for (expr* arg : *jst) 
                if (m.is_bool(arg))
                    result.push_back(mk_not(m, arg));
            return result;
        }

        /**
           Add implied equality as an inequality
         */
        bool add_implied_ineq(bool sign, app* jst) {
            unsigned n = jst->get_num_args();
            if (n < 2)
                return false;
            expr* arg1 = jst->get_arg(n - 2);
            expr* arg2 = jst->get_arg(n - 1);
            rational coeff;
            if (!a.is_numeral(arg1, coeff))
                return false;
            if (!m.is_not(arg2, arg2))
                return false;
            if (!m.is_eq(arg2, arg1, arg2))
                return false;
            if (!sign)
                coeff.neg();
            auto& r = m_ineq;
            linearize(r, coeff, arg1);
            linearize(r, -coeff, arg2);
            m_strict = true;
            return true;
        }

        bool check(app* jst) override {
            reset();
            bool is_bound = jst->get_name() == m_bound;
            bool is_implied_eq = jst->get_name() == m_implied_eq;
            bool is_farkas = jst->get_name() == m_farkas;
            if (!is_farkas && !is_bound && !is_implied_eq) {
                IF_VERBOSE(0, verbose_stream() << "unhandled inference " << mk_pp(jst, m) << "\n");
                return false;
            }
            bool even = true;
            rational coeff;
            expr* x, * y;
            unsigned j = 0, num_le = 0;

            
            for (expr* arg : *jst) {
                if (even) {
                    if (!a.is_numeral(arg, coeff)) {
                        IF_VERBOSE(0, verbose_stream() << "not numeral " << mk_pp(jst, m) << "\n");
                        return false;
                    }
                    if (is_implied_eq) {
                        is_implied_eq = false;
                        if (!coeff.is_unsigned()) {
                            IF_VERBOSE(0, verbose_stream() << "not unsigned " << mk_pp(jst, m) << "\n");
                            return false;
                        }
                        num_le = coeff.get_unsigned();
                        if (!add_implied_ineq(false, jst)) {
                            IF_VERBOSE(0, display(verbose_stream() << "did not add implied eq"));
                            return false;
                        }
                        ++j;
                        continue;
                    }
                }
                else {
                    bool sign = m.is_not(arg, arg);
                    if (a.is_le(arg) || a.is_lt(arg) || a.is_ge(arg) || a.is_gt(arg)) {
                        if (is_bound && j + 1 == jst->get_num_args())
                            add_conseq(coeff, arg, sign);
                        else if (num_le > 0) {
                            add_ineq(coeff, arg, sign);
                            --num_le;
                            if (num_le == 0) {
                                // we processed all the first inequalities,
                                // check that they imply one half of the implied equality.
                                if (!check()) {
                                    // we might have added the wrong direction of the implied equality.
                                    // so try the opposite inequality.
                                    add_implied_ineq(true, jst);
                                    add_implied_ineq(true, jst);
                                    if (check()) {
                                        reset();
                                        add_implied_ineq(false, jst);
                                    }
                                    else {
                                        IF_VERBOSE(0, display(verbose_stream() << "failed to check implied eq "));
                                        return false;
                                    }
                                }
                                else {
                                    reset();
                                    VERIFY(add_implied_ineq(true, jst));
                                }
                            }
                        }
                        else
                            add_ineq(coeff, arg, sign);
                    }
                    else if (m.is_eq(arg, x, y)) {
                        if (is_bound && j + 1 == jst->get_num_args())
                            add_conseq(coeff, arg, sign);
                        else if (sign) 
                            return check(); // it should be an implied equality
                        else
                            add_eq(x, y);
                    }
                    else {
                        IF_VERBOSE(0, verbose_stream() << "not a recognized arithmetical relation " << mk_pp(arg, m) << "\n");
                        return false;
                    }
                }
                even = !even;
                ++j;
            }
            return check();
        }

        void register_plugins(euf::theory_checker& pc) override {
            pc.register_plugin(m_farkas, this);
            pc.register_plugin(m_bound, this);
            pc.register_plugin(m_implied_eq, this);
        }
        
    };

}
