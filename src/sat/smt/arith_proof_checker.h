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
- implied-eq - last literal is a disequality. The literals before imply the corresponding equality.
- bound - last literal is a bound. It is implied by prior literals.

--*/
#pragma once

#include "util/obj_pair_set.h"
#include "ast/ast_trail.h"
#include "ast/arith_decl_plugin.h"
#include "sat/smt/euf_proof_checker.h"


namespace arith {

    class proof_checker : public euf::proof_checker_plugin {
        struct row {
            obj_map<expr, rational> m_coeffs;
            rational m_coeff;
            void reset() {
                m_coeffs.reset();
                m_coeff = 0;
            }
        };
        
        ast_manager& m;
        arith_util a;
        vector<std::pair<rational, expr*>> m_todo;
        bool m_strict = false;
        row m_ineq;
        row m_conseq;
        vector<row> m_eqs;
        vector<row> m_ineqs;
        vector<row> m_diseqs;
        
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
            expr* e1, *e2, *e3;
            for (unsigned i = 0; i < m_todo.size(); ++i) {
                auto [coeff, e] = m_todo[i];
                if (a.is_mul(e, e1, e2) && a.is_numeral(e1, coeff1))
                    m_todo.push_back({coeff*coeff1, e2});
                else if (a.is_mul(e, e1, e2) && a.is_uminus(e1, e3) && a.is_numeral(e3, coeff1))
                    m_todo.push_back({-coeff*coeff1, e2});
                else if (a.is_mul(e, e1, e2) && a.is_numeral(e2, coeff1))
                    m_todo.push_back({coeff*coeff1, e1});
                else if (a.is_add(e))
                    for (expr* arg : *to_app(e))
                        m_todo.push_back({coeff, arg});
                else if (a.is_uminus(e, e1))
                    m_todo.push_back({-coeff, e1});
                else if (a.is_sub(e, e1, e2)) {
                    m_todo.push_back({coeff, e1});
                    m_todo.push_back({-coeff, e2});                
                }
                else if (a.is_numeral(e, coeff1)) 
                    r.m_coeff += coeff*coeff1;
                else if (a.is_uminus(e, e1) && a.is_numeral(e1, coeff1))
                    r.m_coeff -= coeff*coeff1;
                else
                    add(r, e, coeff);
            }
            m_todo.reset();
        }
        
        bool check_ineq(row& r) {
            if (r.m_coeffs.empty() && r.m_coeff > 0)
                return true;
            if (r.m_coeffs.empty() && m_strict && r.m_coeff == 0)
                return true;
            return false;
        }
        
        // triangulate equalities, substitute results into m_ineq, m_conseq.
        void reduce_eq() {
            for (unsigned i = 0; i < m_eqs.size(); ++i) {
                auto& r = m_eqs[i];
                if (r.m_coeffs.empty())
                    continue;
                auto [v, coeff] = *r.m_coeffs.begin();
                for (unsigned j = i + 1; j < m_eqs.size(); ++j)
                    resolve(v, m_eqs[j], coeff, r);
                resolve(v, m_ineq, coeff, r);
                resolve(v, m_conseq, coeff, r);
            }
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
            reduce_eq();
            if (check_ineq(m_ineq))
                return true;
            
            // convert to expression, maybe follows from a cut.
            return false;
        }

        //
        // farkas coefficient is computed for m_conseq 
        // after all inequalities in ineq have been added up
        //
        bool check_bound() {
            reduce_eq();
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

        //
        // checking disequalities is TBD.
        // it has to select only a subset of bounds to justify each inequality.
        // example
        // c <= x <= c, c <= y <= c => x = y
        // for the proof of x <= y use the inequalities x <= c <= y
        // for the proof of y <= x use the inequalities y <= c <= x
        // example
        // x <= y, y <= z, z <= u, u <= x => x = z
        // for the proof of x <= z use the inequalities x <= y, y <= z
        // for the proof of z <= x use the inequalities z <= u, u <= x
        // 
        // so when m_diseqs is non-empty we can't just add inequalities with Farkas coefficients
        // into m_ineq, since coefficients of the usable subset vanish.
        // 

        bool check_diseq() {
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
        proof_checker(ast_manager& m): m(m), a(m) {}

        ~proof_checker() override {}
        
        void reset() {
            m_ineq.reset();
            m_conseq.reset();
            m_eqs.reset();
            m_ineqs.reset();
            m_diseqs.reset();
            m_strict = false;
        }
        
        bool add_ineq(rational const& coeff, expr* e, bool sign) {
            if (!m_diseqs.empty())
                return add_literal(fresh(m_ineqs), abs(coeff), e, sign);
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

        void add_diseq(expr* a, expr* b) {
            row& r = fresh(m_diseqs);
            linearize(r, rational(1), a);
            linearize(r, rational(-1), b);            
        }
        
        bool check() {
            if (!m_diseqs.empty())
                return check_diseq();
            else if (!m_conseq.m_coeffs.empty())
                return check_bound();
            else
                return check_farkas();
        }

        std::ostream& display(std::ostream& out) {
            for (auto & r : m_eqs)
                display_eq(out, r);
            display_ineq(out, m_ineq);
            if (!m_conseq.m_coeffs.empty())
                display_ineq(out, m_conseq);
            return out;
        }

        bool check(expr_ref_vector const& clause, app* jst, expr_ref_vector& units) override {
            reset();
            expr_mark pos, neg;
            for (expr* e : clause)
                if (m.is_not(e, e))
                    neg.mark(e, true);
                else
                    pos.mark(e, true);

            if (jst->get_name() == symbol("farkas")) {
                bool even = true;
                rational coeff;
                expr* x, *y;
                for (expr* arg : *jst) {
                    if (even) {
                        if (!a.is_numeral(arg, coeff)) {
                            IF_VERBOSE(0, verbose_stream() << "not numeral " << mk_pp(jst, m) << "\n");
                            return false;
                        }
                    }
                    else {
                        bool sign = m.is_not(arg, arg);
                        if (a.is_le(arg) || a.is_lt(arg) || a.is_ge(arg) || a.is_gt(arg)) 
                            add_ineq(coeff, arg, sign);
                        else if (m.is_eq(arg, x, y)) {
                            if (sign)
                                add_diseq(x, y);
                            else
                                add_eq(x, y);
                        }
                        else
                            return false;

                        if (sign && !pos.is_marked(arg)) {
                            units.push_back(m.mk_not(arg));
                            pos.mark(arg, false);
                        }
                        else if (!sign && !neg.is_marked(arg)) {
                            units.push_back(arg);
                            neg.mark(arg, false);
                        }
                            
                    }                        
                    even = !even;
                }
                if (check_farkas()) {
                    return true;
                }
                
                IF_VERBOSE(0, verbose_stream() << "did not check farkas\n" << mk_pp(jst, m) << "\n"; display(verbose_stream()); );
                return false;
            }

            // todo: rules for bounds and implied-by

            IF_VERBOSE(0, verbose_stream() << "did not check " << mk_pp(jst, m) << "\n");
            return false;
        }

        void register_plugins(euf::proof_checker& pc) override {
            pc.register_plugin(symbol("farkas"), this);
            pc.register_plugin(symbol("bound"), this);
            pc.register_plugin(symbol("implied-eq"), this);
        }
        
    };

}
