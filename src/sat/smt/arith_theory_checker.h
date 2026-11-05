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
- arith - a theory axiom without coefficients; the arguments are the negated clause literals.
  The clause is accepted when one literal is valid by linear arithmetic over the defining
  identities and bounds of div, mod, rem and / by nonzero numerals, or when it is one of the two
  case splits of abs.

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

        enum rule_type_t {
            cut_t,
            farkas_t,
            implied_eq_t,
            bound_t,
            axiom_t,
            none_t
        };
        
        struct row {
            obj_map<expr, rational> m_coeffs;
            rational m_coeff;
            bool m_strict = false;
            void reset() {
                m_coeffs.reset();
                m_coeff = 0;
                m_strict = false;
            }
            bool is_zero() const {
                return m_coeffs.empty() && m_coeff == 0;
            }
        };
       
        ast_manager& m;
        arith_util   a;
        vector<std::pair<rational, expr *>> m_todo;
        row          m_ineq;
        row          m_conseq;
        vector<row>  m_eqs, m_ineqs;
        symbol       m_farkas = symbol("farkas");
        symbol       m_implied_eq = symbol("implied-eq");
        symbol       m_bound = symbol("bound");
        symbol       m_cut = symbol("cut");
        symbol       m_axiom = symbol("arith");
        expr_ref_vector m_pinned;

        rule_type_t rule_type(app* jst) const {
            if (jst->get_name() == m_cut)
                return cut_t;
            if (jst->get_name() == m_axiom)
                return axiom_t;
            if (jst->get_name() == m_bound)
                return bound_t;
            if (jst->get_name() == m_implied_eq)
                return implied_eq_t;
            if (jst->get_name() == m_farkas)
                return farkas_t;
            return none_t;
        }
        
        
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
            r.m_strict &= !coeff.is_zero();
            for (auto & [v, c] : r.m_coeffs)
                c *= coeff;
            r.m_coeff *= coeff;
        }
        
        // dst <- dst + mul*src
        void add(row& dst, row const& src, rational const& mul) {
            dst.m_strict |= src.m_strict && !mul.is_zero();
            for (auto const& [v, c] : src.m_coeffs)
                add(dst, v, c*mul);
            dst.m_coeff += mul*src.m_coeff;
        }
        
        // dst <- X*dst + Y*src
        // where
        // X = lcm(a,b)/b, Y = -lcm(a,b)/a  if v is integer
        // X = 1/b, Y = -1/a                if v is real
        //
        bool resolve(expr* v, row& dst, rational const& A, row const& src) {
            rational B, x, y;
            if (!dst.m_coeffs.find(v, B))
                return false;
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
            return true;
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
                if (a.is_mul(e))
                    linearize_mul(r, coeff, to_app(e));
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

        /**
         * \brief add mul * (* t1 .. tn) to r, folding the numeral factors into the coefficient.
         * A product with two or more non-numeral factors is nonlinear and is kept as one opaque term.
         */
        void linearize_mul(row& r, rational const& mul, app* e) {
            rational coeff(mul), coeff1;
            expr* x = nullptr;
            for (expr* arg : *e) {
                if (is_numeral(arg, coeff1))
                    coeff *= coeff1;
                else if (!x)
                    x = arg;
                else {
                    add(r, e, mul);
                    return;
                }
            }
            if (x)
                m_todo.push_back({coeff, x});
            else
                r.m_coeff += coeff;
        }

        bool is_numeral(expr* e, rational& n) const {
            return a.is_extended_numeral(e, n);
        }
        
        bool check_ineq(row& r) {
            if (r.m_coeffs.empty() && r.m_coeff > 0)
                return true;
            if (r.m_coeffs.empty() && r.m_strict && r.m_coeff == 0)
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
                for (auto& ineq : m_ineqs)
                    resolve(v, ineq, coeff, r);
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
                    r.m_strict |= !coeff.is_zero();
            }
            else if ((a.is_lt(e, e1, e2) || a.is_gt(e, e2, e1)) && !sign) {
                linearize(r, coeff, e1);
                linearize(r, -coeff, e2);
                if (a.is_int(e1))
                    r.m_coeff += coeff;
                else
                    r.m_strict |= !coeff.is_zero();
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
            if (check_ineq(m_ineq) || check_ineq(m_conseq))
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

        /**
           Check implied equality lemma:

           inequalities & equalities => equality

           
           We may assume the set of inequality assumptions we are given are all tight, non-strict and imply equalities.
           In other words, given a set of inequalities a1x + b1 <= 0, ..., anx + bn <= 0
           the equalities a1x + b1 = 0, ..., anx + bn = 0 are all consequences.

           We use a weaker property: We derive implied equalities by applying exhaustive Fourier-Motzkin
           elimination and then collect the tight 0 <= 0 inequalities that are derived.
           
           Claim: the set of inequalities used to derive 0 <= 0 are all tight equalities.
         */

        svector<std::pair<unsigned, unsigned>> m_deps;
        unsigned_vector m_tight_inequalities;
        uint_set m_ineqs_that_are_eqs;
        
        bool check_implied_eq() {
            if (!reduce_eq())
                return true;
            if (m_conseq.is_zero())
                return true;

            m_eqs.reset();
            m_deps.reset();
            unsigned orig_size = m_ineqs.size();
            m_deps.reserve(orig_size);
            for (unsigned i = 0; i < m_ineqs.size(); ++i) {
                row& r = m_ineqs[i];
                if (r.m_coeffs.empty()) {
                    if (check_ineq(r))
                        return true;
                    if (r.is_zero())
                        m_tight_inequalities.push_back(i);
                    continue;
                }
                auto const& [v, coeff] = *r.m_coeffs.begin();
                unsigned sz = m_ineqs.size();
                
                for (unsigned j = i + 1; j < sz; ++j) {
                    rational B;
                    row& r2 = m_ineqs[j]; 
                    if (!r2.m_coeffs.find(v, B) || (coeff > 0 && B > 0) || (coeff < 0 && B < 0))
                        continue;
                    row& r3 = fresh(m_ineqs);
                    add(r3, m_ineqs[j], rational::one());
                    resolve(v, r3, coeff, m_ineqs[i]);
                    m_deps.push_back({i, j});
                }
                SASSERT(m_deps.size() == m_ineqs.size());
            }

            m_ineqs_that_are_eqs.reset();
            while (!m_tight_inequalities.empty()) {
                unsigned j = m_tight_inequalities.back();
                m_tight_inequalities.pop_back();
                if (m_ineqs_that_are_eqs.contains(j))
                    continue;                
                m_ineqs_that_are_eqs.insert(j);
                if (j < orig_size) {
                    m_eqs.push_back(std::move(m_ineqs[j]));
                }
                else {
                    auto [a, b] = m_deps[j];
                    m_tight_inequalities.push_back(a);
                    m_tight_inequalities.push_back(b);
                }                            
            }
            m_ineqs.reset();

            VERIFY (reduce_eq());

            return m_conseq.is_zero();
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
            if (r.m_strict)
                out << " < 0\n";
            else 
                out << " <= 0\n";
        }

        row& fresh(vector<row>& rows) {
            rows.push_back(row());
            return rows.back();
        }

        /**
         * Theory axioms (rule arith) are the defining facts of the operations the
         * linear solver treats as opaque terms. For a nonzero numeral k:
         *   u = k * (div u k) + (mod u k),  0 <= (mod u k) <= |k| - 1,  k * (u / k) = u,
         *   (rem u k) = (mod u k) when k >= 0 and (rem u k) = -(mod u k) otherwise,
         * and (abs u) is u when u >= 0 and -u when u <= 0.
         */

        // (mod u k) for an integer numeral k other than 0.
        bool is_mod_by_numeral(expr* e, expr*& u, expr*& k, rational& n) const {
            return a.is_mod(e, u, k) && is_numeral(k, n) && n.is_int() && !n.is_zero();
        }

        // Replace every (mod u k) by u - k * (div u k), every (rem u k) by
        // s * (u - k * (div u k)) with s the sign of k, and every (u / k) by u / k
        // for nonzero numerals k.
        void expand_definitions(row& r) {
            vector<std::pair<expr*, rational>> terms;
            for (auto const& [v, c] : r.m_coeffs)
                terms.push_back({ v, c });
            expr* u, * k;
            rational n;
            for (auto const& [v, c] : terms) {
                bool is_rem = a.is_rem(v, u, k) && is_numeral(k, n) && n.is_int() && !n.is_zero();
                if (is_rem || is_mod_by_numeral(v, u, k, n)) {
                    // (rem u k) is (mod u k) when k >= 0 and -(mod u k) otherwise
                    rational s = is_rem && n.is_neg() ? rational(-1) : rational(1);
                    expr* d = a.mk_idiv(u, k);
                    m_pinned.push_back(d);
                    add(r, v, -c);
                    linearize(r, c * s, u);
                    add(r, d, -c * s * n);
                }
                else if (a.is_div(v, u, k) && is_numeral(k, n) && !n.is_zero()) {
                    add(r, v, -c);
                    linearize(r, c / n, u);
                }
            }
        }

        // r <= 0 (r < 0 if strict) has no solution. The only term may be one
        // (mod u k), which ranges over 0 .. |k| - 1.
        bool is_infeasible(row const& r) {
            row s;
            s.m_coeff = r.m_coeff;
            s.m_strict = r.m_strict;
            if (r.m_coeffs.size() == 1) {
                auto const& [v, c] = *r.m_coeffs.begin();
                expr* u, * k;
                rational n;
                if (!is_mod_by_numeral(v, u, k, n))
                    return false;
                if (c < 0)
                    s.m_coeff += c * (abs(n) - 1);
            }
            else if (!r.m_coeffs.empty())
                return false;
            return check_ineq(s);
        }

        // The negation of the literal (sign ? (not e) : e) as r <= 0 or r < 0.
        bool negate_literal(row& r, expr* e, bool sign) {
            return add_literal(r, rational(1), e, !sign);
        }

        bool is_valid_literal(expr* e, bool sign) {
            expr* x, * y;
            if (m.is_true(e) || m.is_false(e))
                return m.is_true(e) != sign;
            if (m.is_eq(e, x, y) && a.is_int_real(x)) {
                row r;
                linearize(r, rational(1), x);
                linearize(r, rational(-1), y);
                expand_definitions(r);
                return sign ? r.m_coeffs.empty() && r.m_coeff != 0 : r.is_zero();
            }
            row r;
            return negate_literal(r, e, sign) && is_infeasible(r);
        }

        // The negation of the literal (sign ? (not e) : e) and a * u < 0 cannot
        // both hold: a positive multiple of a * u plus the negation's row is a
        // constant that is not negative.
        bool implies_nonnegative(expr* e, bool sign, rational const& a_coeff, expr* u) {
            row r, t;
            if (!negate_literal(r, e, sign))
                return false;
            linearize(t, a_coeff, u);
            if (t.m_coeffs.empty())
                return false;
            auto const& [v, c] = *t.m_coeffs.begin();
            rational rc;
            if (!r.m_coeffs.find(v, rc))
                return false;
            rational lambda = -rc / c;
            if (!lambda.is_pos())
                return false;
            add(r, t, lambda);
            return r.m_coeffs.empty() && !r.m_coeff.is_neg();
        }

        // (abs u) = u or (abs u) = -u, with the case condition u >= 0 or u <= 0
        // implied by the negation of another literal of the clause.
        bool is_abs_case(vector<std::pair<expr*, bool>> const& lits) {
            for (unsigned i = 0; i < lits.size(); ++i) {
                auto [e, sign] = lits[i];
                expr* x, * y, * u;
                if (sign || !m.is_eq(e, x, y))
                    continue;
                if (!a.is_abs(x, u)) {
                    std::swap(x, y);
                    if (!a.is_abs(x, u))
                        continue;
                }
                for (int s : { 1, -1 }) {
                    row r;
                    linearize(r, rational(1), y);
                    linearize(r, rational(-s), u);
                    if (!r.is_zero())
                        continue;
                    for (unsigned j = 0; j < lits.size(); ++j)
                        if (j != i && implies_nonnegative(lits[j].first, lits[j].second, rational(s), u))
                            return true;
                }
            }
            return false;
        }

        bool check_axiom(app* jst) {
            vector<std::pair<expr*, bool>> lits;
            for (expr* arg : *jst) {
                if (!m.is_bool(arg))
                    return false;
                if (m.is_true(arg))
                    continue;
                expr* e = arg;
                bool sign = !m.is_not(arg, e);
                if (is_valid_literal(e, sign))
                    return true;
                lits.push_back({ e, sign });
            }
            return is_abs_case(lits);
        }

    public:
        theory_checker(ast_manager& m): 
            m(m),
            a(m),
            m_pinned(m) {}

        void reset() {
            m_pinned.reset();
            m_ineq.reset();
            m_conseq.reset();
            m_eqs.reset();
            m_ineqs.reset();
            m_tight_inequalities.reset();
        }
        
        bool add_ineq(rule_type_t rt, rational const& coeff, expr* e, bool sign) {
            row& r = rt == implied_eq_t ? fresh(m_ineqs) : m_ineq;
            return add_literal(r, abs(coeff), e, sign);            
        }

        bool add_conseq(rational const& coeff, expr* e, bool sign) {
            return add_literal(m_conseq, abs(coeff), e, sign);
        }
        
        void add_eq(expr* a, expr* b) {
            row& r = fresh(m_eqs);
            linearize(r, rational(1), a);
            linearize(r, rational(-1), b);
        }
        
        bool check(rule_type_t rt) {
            switch (rt) {
            case farkas_t:
                return check_farkas();
            case bound_t:
                return check_bound();
            case implied_eq_t:
                return check_implied_eq();
            default:
                return check_bound();
            }
        }

        std::ostream& display(std::ostream& out) {
            for (auto & r : m_eqs)
                display_eq(out, r);
            display_ineq(out, m_ineq);
            if (!m_conseq.m_coeffs.empty())
                display_ineq(out, m_conseq);
            return out;
        }

        // A true argument stands for a literal false at the base level that the
        // logged clause omits (the q = 0 of a division axiom by a numeral q).
        expr_ref_vector clause(app* jst) override {
            expr_ref_vector result(m);
            for (expr* arg : *jst)
                if (m.is_bool(arg) && !m.is_true(arg))
                    result.push_back(mk_not(m, arg));
            return result;
        }

        /**
           Add implied equality as an inequality
         */
        bool add_implied_diseq(bool sign, app* jst) {
            unsigned n = jst->get_num_args();
            if (n < 2)
                return false;
            expr* arg1 = jst->get_arg(n - 2);
            expr* arg2 = jst->get_arg(n - 1);
            rational coeff;
            if (!is_numeral(arg1, coeff) || coeff.is_zero())
                return false;
            if (!m.is_not(arg2, arg2))
                return false;
            if (!m.is_eq(arg2, arg1, arg2))
                return false;
            if (!sign)
                coeff.neg();
            auto& r = m_conseq;
            linearize(r, coeff, arg1);
            linearize(r, -coeff, arg2);
            return true;
        }

        bool check(app* jst) override {
            reset();

            auto rt = rule_type(jst);
            switch (rt) {
            case cut_t:
                return false;
            case axiom_t:
                return check_axiom(jst);
            case none_t:
                IF_VERBOSE(0, verbose_stream() << "unhandled inference " << mk_pp(jst, m) << "\n");
                return false;
            default:
                break;
            }
            bool even = true;
            rational coeff;
            expr* x, * y;
            unsigned j = 0;
            
            for (expr* arg : *jst) {
                
                if (even) {
                    if (!is_numeral(arg, coeff)) {
                        IF_VERBOSE(0, verbose_stream() << "not numeral " << mk_pp(jst, m) << "\n");
                        return false;
                    }
                }
                else {
                    bool sign = m.is_not(arg, arg);
                    if (a.is_le(arg) || a.is_lt(arg) || a.is_ge(arg) || a.is_gt(arg)) {
                        if (rt == bound_t && j + 1 == jst->get_num_args())
                            add_conseq(coeff, arg, sign);
                        else
                            add_ineq(rt, coeff, arg, sign);
                    }
                    else if (m.is_eq(arg, x, y)) {
                        if (rt == bound_t && j + 1 == jst->get_num_args())
                            add_conseq(coeff, arg, sign);
                        else if (rt == implied_eq_t && j + 1 == jst->get_num_args()) 
                            return add_implied_diseq(sign, jst) && check(rt);
                        else if (!sign) 
                            add_eq(x, y);
                        else {
                            IF_VERBOSE(0, verbose_stream() << "unexpected disequality in justification " << mk_pp(arg, m) << "\n");
                            return false;
                        }
                    }
                    else {
                        IF_VERBOSE(0, verbose_stream() << "not a recognized arithmetical relation " << mk_pp(arg, m) << "\n");
                        return false;
                    }
                }
                even = !even;
                ++j;
            }
            // Only the final disequality above may discharge an implied-eq hint.
            return rt != implied_eq_t && check(rt);
        }

        void register_plugins(euf::theory_checker& pc) override {
            pc.register_plugin(m_farkas, this);
            pc.register_plugin(m_bound, this);
            pc.register_plugin(m_implied_eq, this);
            pc.register_plugin(m_cut, this);
            pc.register_plugin(m_axiom, this);
        }
        
    };

}
