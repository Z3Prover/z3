/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    arith_proof_checker.h

Abstract:

    Plugin for checking arithmetic lemmas

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/
#pragma once

#include "util/obj_pair_set.h"
#include "ast/ast_trail.h"
#include "ast/arith_decl_plugin.h"


namespace arith {

    class proof_checker {
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
                if (a.is_mul(e, e1, e2) && a.is_numeral(e1, coeff1))
                    m_todo.push_back({coeff*coeff1, e2});
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

        
    public:
        proof_checker(ast_manager& m): m(m), a(m) {}
        
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
            m_eqs.push_back(row());
            row& r = m_eqs.back();
            linearize(r, rational(1), a);
            linearize(r, rational(-1), b);
        }
        
        bool check() {
            if (!m_conseq.m_coeffs.empty())
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

        
    };

}
