/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    opt_lp_relaxation.cpp

Abstract:

    Linear relaxation of a MaxSMT problem.

Author:

    Lev Nachmanson (levnach) 2026-10-28

--*/

#include <cstring>
#include <algorithm>
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "util/common_msgs.h"
#include "opt/opt_solver.h"
#include "opt/opt_lp_relaxation.h"

namespace opt {

    void lp_relaxation::linear::add(linear const& other, rational const& scale) {
        constant += scale * other.constant;
        for (auto const& [v, c] : other.terms)
            terms.push_back({v, scale * c});
    }

    void lp_relaxation::linear::normalize() {
        std::sort(terms.begin(), terms.end(),
                  [](auto const& x, auto const& y) { return x.first->get_id() < y.first->get_id(); });
        unsigned j = 0;
        for (unsigned i = 0; i < terms.size(); ++i) {
            if (j > 0 && terms[j - 1].first == terms[i].first)
                terms[j - 1].second += terms[i].second;
            else
                terms[j++] = terms[i];
            if (terms[j - 1].second.is_zero())
                --j;
        }
        terms.shrink(j);
    }

    bool lp_relaxation::linear::same_terms(linear const& other) const {
        if (terms.size() != other.terms.size())
            return false;
        for (unsigned i = 0; i < terms.size(); ++i)
            if (terms[i].first != other.terms[i].first || terms[i].second != other.terms[i].second)
                return false;
        return true;
    }

    lp_relaxation::lp_relaxation(ast_manager& m, generic_model_converter& fm, params_ref const& p):
        m(m), m_fm(fm), m_params(p), a(m), pb(m), m_trail(m), m_constraints(m) {}

    app* lp_relaxation::proxy(expr* c) {
        app* r = nullptr;
        if (m_proxies.find(c, r))
            return r;
        r = m.mk_fresh_const("relax", a.mk_real());
        m_trail.push_back(c);
        m_trail.push_back(r);
        m_proxies.insert(c, r);
        if (m.is_bool(c)) {
            m_constraints.push_back(a.mk_ge(r, a.mk_real(0)));
            m_constraints.push_back(a.mk_le(r, a.mk_real(1)));
        }
        return r;
    }

    bool lp_relaxation::is_literal(expr* l) const {
        m.is_not(l, l);
        return is_uninterp_const(l) && m.is_bool(l);
    }

    // b becomes r, not b becomes 1 - r.
    bool lp_relaxation::relax_literal(expr* l, linear& out) {
        bool sign = false;
        while (m.is_not(l, l))
            sign = !sign;
        if (m.is_true(l) || m.is_false(l)) {
            if (m.is_true(l) != sign)
                out.constant += 1;
            return true;
        }
        if (!is_uninterp_const(l) || !m.is_bool(l))
            return false;
        app* r = proxy(l);
        if (sign) {
            out.constant += 1;
            out.terms.push_back({r, rational::minus_one()});
        }
        else
            out.terms.push_back({r, rational::one()});
        return true;
    }

    // Linear term over numerals, numeric constants, and ite over a literal
    // with constant branches: ite(b, x, y) becomes y + (x - y) * r.
    bool lp_relaxation::relax_term(expr* t, rational const& scale, linear& out) {
        rational v;
        expr *x, *y, *c;
        if (a.is_numeral(t, v)) {
            out.constant += scale * v;
            return true;
        }
        if (a.is_add(t)) {
            for (expr* arg : *to_app(t))
                if (!relax_term(arg, scale, out))
                    return false;
            return true;
        }
        if (a.is_sub(t)) {
            app* ap = to_app(t);
            if (ap->get_num_args() == 0)
                return false;
            if (!relax_term(ap->get_arg(0), scale, out))
                return false;
            for (unsigned i = 1; i < ap->get_num_args(); ++i)
                if (!relax_term(ap->get_arg(i), -scale, out))
                    return false;
            return true;
        }
        if (a.is_uminus(t, x))
            return relax_term(x, -scale, out);
        if (a.is_to_real(t, x))
            return relax_term(x, scale, out);
        if (a.is_mul(t)) {
            rational coeff(1);
            expr* var = nullptr;
            for (expr* arg : *to_app(t)) {
                if (a.is_numeral(arg, v))
                    coeff *= v;
                else if (var)
                    return false;
                else
                    var = arg;
            }
            if (!var) {
                out.constant += scale * coeff;
                return true;
            }
            return relax_term(var, scale * coeff, out);
        }
        if (m.is_ite(t, c, x, y)) {
            linear lc, lx, ly;
            if (!relax_literal(c, lc))
                return false;
            if (!relax_term(x, rational::one(), lx) || !lx.is_constant())
                return false;
            if (!relax_term(y, rational::one(), ly) || !ly.is_constant())
                return false;
            out.constant += scale * ly.constant;
            out.add(lc, scale * (lx.constant - ly.constant));
            return true;
        }
        if (is_uninterp_const(t) && a.is_int_real(t)) {
            out.terms.push_back({proxy(t), scale});
            return true;
        }
        return false;
    }

    expr_ref lp_relaxation::mk_expr(linear const& l) {
        expr_ref_vector args(m);
        if (!l.constant.is_zero())
            args.push_back(a.mk_real(l.constant));
        for (auto const& [v, c] : l.terms) {
            if (c.is_zero())
                continue;
            if (c.is_one())
                args.push_back(v);
            else
                args.push_back(a.mk_mul(a.mk_real(c), v));
        }
        if (args.empty())
            args.push_back(a.mk_real(0));
        return expr_ref(a.mk_add(args.size(), args.data()), m);
    }

    // l < 0, l = 0, or l <= 0
    void lp_relaxation::add_constraint(linear const& l, bool strict_lt, bool eq) {
        expr_ref e = mk_expr(l);
        expr_ref zero(a.mk_real(0), m);
        if (eq)
            m_constraints.push_back(m.mk_eq(e, zero));
        else if (strict_lt)
            m_constraints.push_back(a.mk_lt(e, zero));
        else
            m_constraints.push_back(a.mk_le(e, zero));
    }

    // Comparison as one or two bounds l <= 0 or l < 0. Over integers x < y is x + 1 <= y.
    bool lp_relaxation::comparison_bounds(expr* f, bool sign, vector<bound>& out) {
        expr *x, *y;
        bool le = false, lt = false, eq = false;
        if (a.is_le(f, x, y))
            le = true;
        else if (a.is_ge(f, x, y)) {
            std::swap(x, y);
            le = true;
        }
        else if (a.is_lt(f, x, y))
            lt = true;
        else if (a.is_gt(f, x, y)) {
            std::swap(x, y);
            lt = true;
        }
        else if (m.is_eq(f, x, y) && a.is_int_real(x))
            eq = true;
        else
            return false;
        if (sign) {
            if (eq)
                return false;
            // not (x <= y) is y < x; not (x < y) is y <= x
            std::swap(x, y);
            std::swap(le, lt);
        }
        linear l;
        if (!relax_term(x, rational::one(), l) || !relax_term(y, rational::minus_one(), l))
            return false;
        if (lt && a.is_int(x)) {
            l.constant += 1;
            lt = false;
        }
        l.normalize();
        out.push_back({l, lt});
        if (eq) {
            linear neg;
            neg.add(l, rational::minus_one());
            neg.normalize();
            out.push_back({neg, false});
        }
        return true;
    }

    bool lp_relaxation::relax_comparison(expr* f, bool sign) {
        vector<bound> bounds;
        if (!comparison_bounds(f, sign, bounds))
            return false;
        for (bound const& b : bounds)
            add_constraint(b.l, b.strict, false);
        return true;
    }

    // Pseudo-Boolean atom. A negated atom with integral coefficients and
    // bound is the complementary atom with the bound moved by one.
    bool lp_relaxation::relax_pb(expr* f, bool sign) {
        rational k;
        bool le = false, eq = false;
        bool unit = pb.is_at_most_k(f) || pb.is_at_least_k(f);
        if (pb.is_at_most_k(f, k) || pb.is_le(f, k))
            le = true;
        else if (pb.is_at_least_k(f, k) || pb.is_ge(f, k))
            le = false;
        else if (pb.is_eq(f, k))
            eq = true;
        else
            return false;
        if (sign && (eq || !k.is_int()))
            return false;
        app* ap = to_app(f);
        linear l;
        for (unsigned i = 0; i < ap->get_num_args(); ++i) {
            rational c = unit ? rational::one() : pb.get_coeff(f, i);
            if (sign && !c.is_int())
                return false;
            linear lit;
            if (!relax_literal(ap->get_arg(i), lit))
                return false;
            l.add(lit, c);
        }
        if (sign) {
            // not (sum <= k) is sum >= k + 1; not (sum >= k) is sum <= k - 1
            k += le ? rational::one() : rational::minus_one();
            le = !le;
        }
        // sum <= k is sum - k <= 0; sum >= k is k - sum <= 0
        if (!le && !eq) {
            linear neg;
            neg.add(l, rational::minus_one());
            neg.constant += k;
            add_constraint(neg, false, false);
        }
        else {
            l.constant -= k;
            add_constraint(l, false, eq);
        }
        return true;
    }

    // Clause over literals: the relaxed literals sum to at least one.
    bool lp_relaxation::relax_clause(unsigned n, expr* const* lits) {
        linear l;
        for (unsigned i = 0; i < n; ++i)
            if (!relax_literal(lits[i], l))
                return false;
        linear neg;
        neg.add(l, rational::minus_one());
        neg.constant += 1;
        add_constraint(neg, false, false);
        return true;
    }

    // A clause of one literal and one linear atom: the atom holds when the
    // literal is false. The bounds are kept by the Boolean constant and its
    // polarity for relax_indicators.
    bool lp_relaxation::keep_indicator(unsigned n, expr* const* lits) {
        if (n != 2)
            return false;
        expr* lit = nullptr;
        expr* atom = nullptr;
        for (unsigned i = 0; i < 2; ++i) {
            if (is_literal(lits[i]) && !lit)
                lit = lits[i];
            else
                atom = lits[i];
        }
        if (!lit || !atom)
            return false;
        vector<bound> bounds;
        if (!comparison_bounds(atom, false, bounds))
            return false;
        // the atom is implied by the negation of the literal
        bool implied_by_true = m.is_not(lit, lit);
        unsigned index;
        if (!m_indicator_index.find(lit, index)) {
            index = m_indicators.size();
            m_indicators.push_back(indicator_group());
            m_indicator_index.insert(lit, index);
            m_trail.push_back(lit);
        }
        auto& group = m_indicators[index];
        auto& side = implied_by_true ? group.when_true : group.when_false;
        for (bound const& b : bounds)
            side.push_back(b);
        return true;
    }

    // b implies L + c1 <= 0 and not b implies L + c0 <= 0 give
    // L + c0 + (c1 - c0) * r <= 0, since r is 1 exactly when b holds.
    // Bounds without a partner on the opposite polarity are dropped.
    void lp_relaxation::relax_indicators() {
        for (auto const& [b, index] : m_indicator_index) {
            indicator_group const& group = m_indicators[index];
            linear r;
            relax_literal(b, r);
            svector<bool> used_false(group.when_false.size(), false);
            for (bound const& t : group.when_true) {
                bool matched = false;
                for (unsigned j = 0; j < group.when_false.size(); ++j) {
                    bound const& f = group.when_false[j];
                    if (!t.l.same_terms(f.l))
                        continue;
                    linear l = f.l;
                    l.add(r, t.l.constant - f.l.constant);
                    add_constraint(l, t.strict && f.strict, false);
                    matched = true;
                    used_false[j] = true;
                }
                if (!matched)
                    ++m_num_dropped;
            }
            for (unsigned j = 0; j < group.when_false.size(); ++j)
                if (!used_false[j])
                    ++m_num_dropped;
        }
        m_indicator_index.reset();
        m_indicators.reset();
    }

    bool lp_relaxation::relax_formula(expr* f, bool sign) {
        expr *x, *y;
        while (m.is_not(f, f))
            sign = !sign;
        if (m.is_true(f) || m.is_false(f))
            return m.is_true(f) != sign;
        if (m.is_and(f)) {
            if (sign) {
                expr_ref_vector lits(m);
                for (expr* arg : *to_app(f))
                    lits.push_back(mk_not(m, arg));
                return relax_clause(lits.size(), lits.data());
            }
            bool all = true;
            for (expr* arg : *to_app(f))
                all = relax_formula(arg, false) && all;
            return all;
        }
        if (m.is_or(f)) {
            app* ap = to_app(f);
            if (!sign)
                return relax_clause(ap->get_num_args(), ap->get_args()) ||
                       keep_indicator(ap->get_num_args(), ap->get_args());
            bool all = true;
            for (expr* arg : *ap)
                all = relax_formula(arg, true) && all;
            return all;
        }
        if (m.is_implies(f, x, y)) {
            if (sign)
                return relax_formula(x, false) && relax_formula(y, true);
            expr_ref nx(mk_not(m, x), m);
            expr* lits[2] = { nx.get(), y };
            return relax_clause(2, lits) || keep_indicator(2, lits);
        }
        if (m.is_eq(f, x, y) && m.is_bool(x)) {
            if (sign || !is_literal(x) || !is_literal(y))
                return false;
            linear l;
            relax_literal(x, l);
            linear ly;
            relax_literal(y, ly);
            l.add(ly, rational::minus_one());
            add_constraint(l, false, true);
            return true;
        }
        if (is_uninterp_const(f) && m.is_bool(f)) {
            linear l;
            relax_literal(f, l);
            l.constant -= sign ? rational::zero() : rational::one();
            add_constraint(l, false, true);
            return true;
        }
        if (pb.is_at_most_k(f) || pb.is_at_least_k(f) || pb.is_le(f) || pb.is_ge(f) || pb.is_eq(f))
            return relax_pb(f, sign);
        return relax_comparison(f, sign);
    }

    bool lp_relaxation::add_hard(expr* f) {
        if (relax_formula(f, false))
            return true;
        ++m_num_dropped;
        return false;
    }

    bool lp_relaxation::eval(model& mdl, linear const& l, rational& value) {
        value = l.constant;
        for (auto const& [v, c] : l.terms) {
            expr_ref val(mdl(v), m);
            rational r;
            if (!a.is_numeral(val, r))
                return false;
            value += c * r;
        }
        return true;
    }

    // Every cost is a sum of soft weights, so a multiple of their greatest common divisor.
    rational lp_relaxation::lattice_step(vector<soft> const& softs) {
        rational den(1);
        for (soft const& s : softs)
            den = lcm(den, denominator(s.weight));
        rational g(0);
        for (soft const& s : softs)
            g = gcd(g, s.weight * den);
        return g / den;
    }

    lp_relaxation::result lp_relaxation::minimize_cost(vector<soft> const& softs, unsigned rlimit) {
        result res;
        relax_indicators();
        linear satisfied;
        rational literal_weight(0);
        vector<std::pair<unsigned, linear>> literals;
        for (unsigned i = 0; i < softs.size(); ++i) {
            soft const& s = softs[i];
            if (!is_literal(s.s))
                continue;
            linear l;
            VERIFY(relax_literal(s.s, l));
            satisfied.add(l, s.weight);
            literal_weight += s.weight;
            literals.push_back({i, l});
        }
        if (literals.empty())
            return res;

        opt_solver solver(m, m_params, m_fm);
        for (expr* c : m_constraints)
            solver.assert_expr(c);
        expr_ref objective = mk_expr(satisfied);
        if (!is_app(objective) || solver.add_objective(to_app(objective)) == smt::null_theory_var)
            return res;

        unsigned const max_climb_rounds = 64;
        lbool is_sat = l_undef;
        inf_eps value;
        model_ref mdl;
        bool certified = false;
        bool external_cancel = false;
        // The arithmetic solver's maximum is a hint over its current
        // tableau. A strict cut above the hint that is unsatisfiable
        // certifies the hint as the maximum; a satisfiable cut moves the
        // tableau to a better vertex and the climb repeats.
        unsigned num_cuts = 0;
        auto run = [&]() {
            is_sat = solver.check_sat(0, nullptr);
            if (is_sat != l_true)
                return;
            for (unsigned round = 0; round < max_climb_rounds; ++round) {
                expr_ref blocker(m);
                auto maximized = solver.maximize_objective(0, blocker, false, false);
                value = maximized.hint;
                if (!value.is_finite() || value.get_infinitesimal().is_pos()) {
                    is_sat = l_undef;
                    return;
                }
                solver.get_model(mdl);
                solver.push();
                ++num_cuts;
                solver.assert_expr(a.mk_gt(objective, a.mk_real(value.get_rational())));
                lbool above = solver.check_sat(0, nullptr);
                if (above == l_false) {
                    certified = true;
                    return;
                }
                if (above != l_true)
                    return;
            }
        };
        if (rlimit) {
            scoped_rlimit budget(m.limit(), rlimit);
            try {
                run();
            }
            catch (z3_exception&) {
                external_cancel = m.limit().get_cancel_msg() == Z3_CANCELED_MSG;
                is_sat = l_undef;
            }
        }
        else {
            try {
                run();
            }
            catch (z3_exception&) {
                is_sat = l_undef;
            }
        }
        if (num_cuts > 0)
            solver.pop(num_cuts);
        if (external_cancel)
            m.limit().cancel();
        IF_VERBOSE(10, verbose_stream() << "(opt.relaxation :constraints " << m_constraints.size()
                   << " :sat " << is_sat << " :value " << value << " :certified " << certified << ")\n";);
        if (is_sat != l_true || !certified || !mdl)
            return res;

        // cost >= weight of the soft literals - largest relaxed satisfied weight
        rational bound = literal_weight - value.get_rational();
        rational step = lattice_step(softs);
        if (step.is_pos())
            bound = step * ceil(bound / step);
        if (bound.is_neg())
            bound = rational::zero();
        res.lower = bound;
        res.status = l_true;
        for (auto const& [i, l] : literals) {
            rational v;
            if (!eval(*mdl, l, v))
                continue;
            if (v.is_one())
                res.rounding.push_back({i, true});
            else if (v.is_zero())
                res.rounding.push_back({i, false});
        }
        return res;
    }
}
