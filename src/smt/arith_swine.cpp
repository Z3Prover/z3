/*++
Copyright (c) 2026 Microsoft Corporation
--*/
#include "smt/arith_swine.h"
#include "ast/ast_util.h"
#include "util/statistics.h"

namespace smt {

expr_ref arith_swine::num(rational const& n) {
    return expr_ref(a.mk_int(n), m);
}

bool arith_swine::add(unsigned kind, expr* lemma, expr_ref_vector& lemmas) {
    expr_ref f(lemma, m);
    m_rw(f);
    if (m.is_true(f))
        return false;
    lemmas.push_back(f);
    ++m_lemmas[kind];
    return true;
}

bool arith_swine::compute_power(rational const& x, rational const& y, rational& result) {
    SASSERT(x.is_int() && y.is_int() && y >= 0);
    if (y.is_zero() || x.is_one())
        result = rational(1);
    else if (x.is_zero())
        result = rational(0);
    else if (x.is_minus_one())
        result = y.is_even() ? rational(1) : rational(-1);
    else {
        // Do not materialize enormous coefficients just to reject a candidate.
        unsigned max_bits = 1u << 20;
        if (!y.is_unsigned() || y > rational(max_bits / x.bitsize()))
            return false;
        rational base = x;
        unsigned exponent = y.get_unsigned();
        result = rational(1);
        while (exponent) {
            if (!m.inc(1 + base.bitsize() / 32))
                return false;
            if (exponent & 1)
                result *= base;
            exponent >>= 1;
            if (exponent)
                base *= base;
        }
    }
    return true;
}

lbool arith_swine::check_model(vector<power> const& powers) {
    bool incomplete = false;
    for (auto const& p : powers) {
        if (!m.inc())
            return l_undef;
        rational exponent = abs(p.y), expected;
        if (abs(p.x) >= 2 && exponent > rational(p.value.bitsize() + 1))
            return l_false;
        if (!compute_power(p.x, exponent, expected))
            incomplete = true;
        else if (expected != p.value)
            return l_false;
    }
    return incomplete ? l_undef : l_true;
}

void arith_swine::symmetry(vector<power> const& powers, value_fn const& value, expr_ref_vector& lemmas) {
    expr_ref zero = num(rational(0)), two = num(rational(2)), one = num(rational(1));
    for (auto const& p : powers) {
        if (p.x >= 0 && p.y >= 0)
            continue;
        expr_ref base(p.base, m), exponent(p.exponent, m);
        expr_ref_vector guards(m);
        if (p.x < 0) {
            base = a.mk_uminus(base);
            guards.push_back(a.mk_lt(p.base, zero));
        }
        if (p.y < 0) {
            exponent = a.mk_uminus(exponent);
            guards.push_back(a.mk_lt(p.exponent, zero));
        }
        expr_ref normalized(a.mk_power(base, exponent), m);
        m_rw(normalized);
        rational v;
        bool odd = !p.y.is_even();
        if (value(normalized, v) && p.value == (p.x < 0 && odd ? -v : v))
            continue;
        expr_ref rhs(normalized, m);
        if (p.x < 0) {
            expr_ref remainder(a.mk_mod(p.exponent, two), m);
            expr_ref is_odd(m.mk_eq(remainder, one), m);
            expr_ref negative(a.mk_uminus(normalized), m);
            rhs = m.mk_ite(is_odd, negative, normalized);
        }
        expr_ref guard(mk_and(guards), m);
        expr_ref equality(m.mk_eq(p.term, rhs), m);
        add(0, m.mk_implies(guard, equality), lemmas);
    }
}

void arith_swine::monotonicity(vector<power> const& powers, expr_ref_vector& lemmas) {
    expr_ref one = num(rational(1)), zero = num(rational(0));
    for (auto const& p : powers) {
        if (p.x <= 1 || p.y <= 0)
            continue;
        for (auto const& q : powers) {
            if (!m.inc())
                return;
            if (q.x < p.x || q.y < p.y || (q.x == p.x && q.y == p.y) || q.value > p.value)
                continue;
            expr_ref_vector guards(m);
            guards.push_back(a.mk_gt(p.base, one));
            guards.push_back(a.mk_gt(p.exponent, zero));
            guards.push_back(a.mk_ge(q.base, p.base));
            guards.push_back(a.mk_ge(q.exponent, p.exponent));
            expr_ref larger_base(a.mk_gt(q.base, p.base), m);
            expr_ref larger_exponent(a.mk_gt(q.exponent, p.exponent), m);
            guards.push_back(m.mk_or(larger_base, larger_exponent));
            expr_ref guard(mk_and(guards), m);
            expr_ref conclusion(a.mk_gt(q.term, p.term), m);
            add(1, m.mk_implies(guard, conclusion), lemmas);
        }
    }
}

void arith_swine::bounding(vector<power> const& powers, expr_ref_vector& lemmas) {
    expr_ref zero = num(rational(0)), one = num(rational(1)), four = num(rational(4));
    for (auto const& p : powers) {
        expr_ref premise(m), conclusion(m);
        if (p.y == 0 && p.value != 1) {
            premise = m.mk_eq(p.exponent, zero);
            conclusion = m.mk_eq(p.term, one);
        }
        else if (p.y == 1 && p.value != p.x) {
            premise = m.mk_eq(p.exponent, one);
            conclusion = m.mk_eq(p.term, p.base);
        }
        else if ((p.x == 0 && p.y != 0) != (p.value == 0)) {
            expr_ref base_zero(m.mk_eq(p.base, zero), m);
            expr_ref exponent_zero(m.mk_eq(p.exponent, zero), m);
            expr_ref exponent_nonzero(m.mk_not(exponent_zero), m);
            premise = m.mk_and(base_zero, exponent_nonzero);
            conclusion = m.mk_eq(p.term, zero);
            add(2, m.mk_eq(premise, conclusion), lemmas);
            continue;
        }
        else if (p.x == 1 && p.value != 1) {
            premise = m.mk_eq(p.base, one);
            conclusion = m.mk_eq(p.term, one);
        }
        else if (p.x > 0 && p.value < 1) {
            premise = a.mk_gt(p.base, zero);
            conclusion = a.mk_ge(p.term, one);
        }
        else if (p.x > 1 && p.y > 1 && p.x + p.y > 4 && p.value <= p.x * p.y + 1) {
            expr_ref sum(a.mk_add(p.base, p.exponent), m);
            expr_ref product(a.mk_mul(p.base, p.exponent), m);
            expr_ref bound(a.mk_add(product, one), m);
            expr_ref_vector guards(m);
            guards.push_back(a.mk_gt(p.base, one));
            guards.push_back(a.mk_gt(p.exponent, one));
            guards.push_back(a.mk_gt(sum, four));
            premise = mk_and(guards);
            conclusion = a.mk_gt(p.term, bound);
        }
        else
            continue;
        add(2, m.mk_implies(premise, conclusion), lemmas);
    }
}

void arith_swine::prime(vector<power> const& powers, expr_ref_vector& lemmas) {
    expr_ref zero = num(rational(0));
    for (auto const& p : powers) {
        if (p.x < 2 || p.value < 2 || p.y == 0)
            continue;
        rational x = p.x, v = p.value, divisor(2), witness(0);
        while (x != v && (x > 1 || v > 1)) {
            if (!m.inc())
                return;
            if (divisor * divisor > x && divisor * divisor > v) {
                witness = x > 1 ? x : v;
                break;
            }
            bool dx = mod(x, divisor).is_zero(), dv = mod(v, divisor).is_zero();
            if (dx != dv) {
                witness = divisor;
                break;
            }
            while (x > 1 && mod(x, divisor).is_zero())
                x /= divisor;
            while (v > 1 && mod(v, divisor).is_zero())
                v /= divisor;
            divisor += divisor == 2 ? rational(1) : rational(2);
        }
        if (witness == 0)
            continue;
        expr_ref d = num(witness);
        expr_ref base_mod(a.mk_mod(p.base, d), m);
        expr_ref result_mod(a.mk_mod(p.term, d), m);
        expr_ref divides_base(m.mk_eq(base_mod, zero), m);
        expr_ref divides_result(m.mk_eq(result_mod, zero), m);
        expr_ref exponent_zero(m.mk_eq(p.exponent, zero), m);
        expr_ref nonzero(m.mk_not(exponent_zero), m);
        expr_ref rhs(m.mk_and(divides_base, nonzero), m);
        add(3, m.mk_eq(divides_result, rhs), lemmas);
    }
}

void arith_swine::induction(vector<power> const& powers, expr_ref_vector& lemmas) {
    expr_ref zero = num(rational(0));
    for (auto const& p : powers) {
        if (p.y < 0)
            continue;
        for (auto const& q : powers) {
            if (!m.inc())
                return;
            if (p.x != q.x || q.y <= p.y)
                continue;
            rational delta = q.y - p.y, factor;
            if (!compute_power(p.x, delta, factor) || q.value == p.value * factor)
                continue;
            expr_ref d = num(delta);
            expr_ref_vector guards(m);
            guards.push_back(m.mk_eq(p.base, q.base));
            guards.push_back(a.mk_ge(p.exponent, zero));
            expr_ref base_power(m);
            rational numeral;
            if (a.is_numeral(p.base, numeral))
                base_power = num(factor);
            else if (delta.is_unsigned() && delta <= 64) {
                expr_ref_vector factors(m);
                for (unsigned i = 0; i < delta.get_unsigned(); ++i)
                    factors.push_back(p.base);
                base_power = a.mk_mul_simplify(factors);
            }
            else {
                // Specialize large unrollings instead of introducing more exp terms.
                expr_ref base = num(p.x);
                guards.push_back(m.mk_eq(p.base, base));
                base_power = num(factor);
            }
            expr_ref rhs(a.mk_mul(p.term, base_power), m);
            expr_ref difference(a.mk_sub(q.exponent, p.exponent), m);
            guards.push_back(m.mk_eq(difference, d));
            expr_ref guard(mk_and(guards), m);
            expr_ref conclusion(m.mk_eq(q.term, rhs), m);
            add(4, m.mk_implies(guard, conclusion), lemmas);
        }
    }
}

expr_ref arith_swine::interpolant(expr* x, expr* y, point const& lo, point const& hi,
                                 rational& denominator, bool& success) {
    rational f00, f01, f10, f11;
    success = compute_power(lo.x, lo.y, f00) && compute_power(lo.x, hi.y, f01) &&
        compute_power(hi.x, lo.y, f10) && compute_power(hi.x, hi.y, f11);
    if (!success)
        return expr_ref(m);
    rational dx = hi.x == lo.x ? rational(1) : hi.x - lo.x;
    rational dy = hi.y == lo.y ? rational(1) : hi.y - lo.y;
    denominator = dx * dy;
    expr_ref x0 = num(lo.x), y0 = num(lo.y);
    expr_ref x_offset(a.mk_sub(x, x0), m), y_offset(a.mk_sub(y, y0), m);
    expr_ref k0 = num(dx * f00), k1 = num(dx * f01);
    expr_ref slope0 = num(f10 - f00), slope1 = num(f11 - f01);
    expr_ref linear0(a.mk_mul(slope0, x_offset), m), linear1(a.mk_mul(slope1, x_offset), m);
    expr_ref lower(a.mk_add(k0, linear0), m), upper(a.mk_add(k1, linear1), m);
    expr_ref dy_expr = num(dy);
    expr_ref constant(a.mk_mul(dy_expr, lower), m);
    expr_ref difference(a.mk_sub(upper, lower), m);
    expr_ref product(a.mk_mul(difference, y_offset), m);
    return expr_ref(a.mk_add(constant, product), m);
}

void arith_swine::interpolation(vector<power> const& powers, expr_ref_vector& lemmas) {
    expr_ref one = num(rational(1));
    for (auto const& p : powers) {
        if (p.x <= 0 || p.y <= 0)
            continue;
        rational expected;
        point anchor{p.x, p.y};
        if (!compute_power(anchor.x, anchor.y, expected)) {
            // A smaller secant can still refute a small, spurious result.
            anchor.x = rational(2);
            anchor.y = std::min(p.y, rational(p.value.bitsize() + 1));
            if (!compute_power(anchor.x, anchor.y, expected))
                continue;
        }
        else if (expected == p.value)
            continue;
        point lo = anchor, hi = anchor;
        bool upper = expected < p.value;
        if (upper) {
            if (anchor.x != p.x || anchor.y != p.y)
                continue;
            rational distance;
            bool found = false;
            for (auto const& previous : m_points) {
                rational d = abs(p.x - previous.x) + abs(p.y - previous.y);
                if (!found || d < distance) {
                    distance = d;
                    lo = {std::min(p.x, previous.x), std::min(p.y, previous.y)};
                    hi = {std::max(p.x, previous.x), std::max(p.y, previous.y)};
                    found = true;
                }
            }
        }
        else
            hi = {lo.x + 1, lo.y + 1};
        rational denominator;
        bool success;
        expr_ref rhs = interpolant(p.base, p.exponent, lo, hi, denominator, success);
        if (!success)
            continue;
        if (!upper && (anchor.x != p.x || anchor.y != p.y)) {
            rational f0, f1, g0, g1;
            if (!compute_power(lo.x, lo.y, f0) || !compute_power(hi.x, lo.y, f1) ||
                !compute_power(lo.x, hi.y, g0) || !compute_power(hi.x, hi.y, g1))
                continue;
            rational lower = f0 + (f1 - f0) * (p.x - lo.x);
            rational higher = g0 + (g1 - g0) * (p.x - lo.x);
            if (lower + (higher - lower) * (p.y - lo.y) <= p.value)
                continue;
        }
        expr_ref scale = num(denominator);
        expr_ref lhs(a.mk_mul(scale, p.term), m);
        expr_ref_vector guards(m);
        expr_ref x0 = num(lo.x), y0 = num(lo.y);
        guards.push_back(a.mk_ge(p.base, upper ? x0.get() : one.get()));
        guards.push_back(a.mk_ge(p.exponent, y0));
        if (upper) {
            expr_ref x1 = num(hi.x), y1 = num(hi.y);
            guards.push_back(a.mk_le(p.base, x1));
            guards.push_back(a.mk_le(p.exponent, y1));
        }
        expr_ref guard(mk_and(guards), m);
        expr_ref conclusion(upper ? a.mk_le(lhs, rhs) : a.mk_ge(lhs, rhs), m);
        add(5, m.mk_implies(guard, conclusion), lemmas);
        if (anchor.x == p.x && anchor.y == p.y)
            m_points.push_back(anchor);
    }
}

lbool arith_swine::check(vector<power> const& powers, value_fn const& value, expr_ref_vector& lemmas) {
    lbool result = check_model(powers);
    if (result == l_true)
        return result;
    symmetry(powers, value, lemmas);
    if (lemmas.empty())
        bounding(powers, lemmas);
    if (lemmas.empty())
        monotonicity(powers, lemmas);
    if (lemmas.empty()) {
        prime(powers, lemmas);
        induction(powers, lemmas);
        interpolation(powers, lemmas);
    }
    return lemmas.empty() ? l_undef : l_false;
}

void arith_swine::reset() {
    m_points.reset();
    for (auto& n : m_lemmas)
        n = 0;
}

void arith_swine::collect_statistics(::statistics& st) const {
    char const* names[] = {"arith-power-symmetry", "arith-power-monotonicity", "arith-power-bounding",
                          "arith-power-prime", "arith-power-induction", "arith-power-interpolation"};
    for (unsigned i = 0; i < 6; ++i)
        st.update(names[i], m_lemmas[i]);
}
}
