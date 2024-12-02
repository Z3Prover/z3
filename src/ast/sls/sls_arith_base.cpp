/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    sls_arith_base.cpp

Abstract:

    Local search dispatch for arithmetic

Author:

    Nikolaj Bjorner (nbjorner) 2023-02-07

    Uses quadratic solver method from nia_ls in hybrid-smt
    (with a bug fix for when order of roots are swapped)
    Other features from nia_ls are also used as a starting point, 
    such as tabu and fallbacks.

Todo:

- add fairness for which variable to flip and direction (by age fifo).
  - maintain age per variable, per sign

- include more general tabu measure
  - 

- random walk when there is no applicable update
  - repair_down can fail repeatedely. Then allow a mode to reset arguments similar to 
    repair of literals.

- avoid overflow for nested products

Done:
- add tabu for flipping variable back to the same value.
  - remember last variable/delta and block -delta = last_delta && last_variable = current_variable
- include measures for bounded updates
  - per variable maintain increasing range 

--*/

#include "ast/sls/sls_arith_base.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"
#include <cmath>

namespace sls {

    template<typename num_t>
    bool arith_base<num_t>::ineq::is_true() const {
        switch (m_op) {
        case ineq_kind::LE:
            return m_args_value <= 0;
        case ineq_kind::EQ:
            return m_args_value == 0;
        default:
            return m_args_value < 0;
        }
    }

    template<typename num_t>
    std::ostream& arith_base<num_t>::ineq::display(std::ostream& out) const {
        bool first = true;
        unsigned j = 0;
        for (auto const& [c, v] : this->m_args) {
            out << (first ? (c > 0 ? "" : "-") : (c > 0 ? " + " : " - "));
            bool first2 = abs(c) == 1;
            if (abs(c) != 1)
                out << abs(c);
            auto const& m = this->m_monomials[j];

            for (auto [w, p] : m) {
                out << (first2 ? "" : " * ") << "v" << w;
                if (p > 1)
                    out << "^" << p;
                first2 = false;
            }
            first = false;
            ++j;
        }
        if (this->m_coeff != 0)
            out << " + " << this->m_coeff;
        switch (m_op) {
        case ineq_kind::LE:
            out << " <= " << 0 << "(" << m_args_value << ")";
            break;
        case ineq_kind::EQ:
            out << " == " << 0 << "(" << m_args_value << ")";
            break;
        default:
            out << " < " << 0 << "(" << m_args_value << ")";
            break;
        }
#if 0
        for (auto const& [x, nl] : this->m_nonlinear) {
            if (nl.size() == 1 && nl[0].v == x)
                continue;
            for (auto const& [v, c, p] : nl) {
                out << " v" << x; 
                if (p > 1) out << "^" << p;
                out << " in v" << v;
            }
        }
#endif
        return out;
    }    

    template<typename num_t>
    arith_base<num_t>::arith_base(context& ctx) :
        plugin(ctx),
        a(m) {
        m_fid = a.get_family_id();
    }

    template<typename num_t>
    void arith_base<num_t>::save_best_values() {
        for (auto& v : m_vars)
            v.set_best_value(v.value());
        check_ineqs();
    }

    // distance to true
    template<typename num_t>
    num_t arith_base<num_t>::dtt(bool sign, num_t const& args, ineq const& ineq) const {
        switch (ineq.m_op) {
        case ineq_kind::LE:
            if (sign) {
                if (args + ineq.m_coeff <= 0)
                    return -ineq.m_coeff - args + 1;
                return num_t(0);
            }
            if (args + ineq.m_coeff <= 0)
                return num_t(0);
            return args + ineq.m_coeff;
        case ineq_kind::EQ:
            if (sign) {
                if (args + ineq.m_coeff == 0)
                    return num_t(1);
                return num_t(0);
            }
            if (args + ineq.m_coeff == 0)
                return num_t(0);
            return num_t(1);
        case ineq_kind::LT:
            if (sign) {
                if (args + ineq.m_coeff < 0)
                    return -ineq.m_coeff - args;
                return num_t(0);
            }
            if (args + ineq.m_coeff < 0)
                return num_t(0);
            return args + ineq.m_coeff + 1;
        default:
            UNREACHABLE();
            return num_t(0);
        }
    }

    //
    // dtt is high overhead. It walks ineq.m_args
    // m_vars[w].m_value can be computed outside and shared among calls
    // different data-structures for storing coefficients
    // 
    template<typename num_t>
    num_t arith_base<num_t>::dtt(bool sign, ineq const& ineq, var_t v, num_t const& new_value) const {
        for (auto const& [coeff, w] : ineq.m_args)
            if (w == v) 
                return dtt(sign, ineq.m_args_value + coeff * (new_value - m_vars[v].value()), ineq);            
        return num_t(1);
    }

    template<typename num_t>
    num_t arith_base<num_t>::dtt(bool sign, ineq const& ineq, num_t const& coeff, num_t const& delta) const {
        return dtt(sign, ineq.m_args_value + coeff * delta, ineq);
    }

    template<typename num_t>
    num_t arith_base<num_t>::divide(var_t v, num_t const& delta, num_t const& coeff) {
        if (is_int(v))
            return div(delta + abs(coeff) - 1, coeff);
        else
            return delta / coeff;        
    }

    template<typename num_t>
    num_t arith_base<num_t>::divide_floor(var_t v, num_t const& a, num_t const& b) {
        if (!is_int(v))
            return a / b;
        if (b > 0 && a >= 0)
            return div(a, b);
        else if (b > 0)
            return -div(-a + b - 1, b);
        else if (a > 0)
            return -div(a - b - 1, -b);
        else
            return div(-a, -b);
    }

    template<typename num_t>
    num_t arith_base<num_t>::divide_ceil(var_t v, num_t const& a, num_t const& b) {
        if (!is_int(v))
            return a / b;
        if (b > 0 && a >= 0)
            return div(a + b - 1, b);
        else if (b > 0)
            return -div(-a, b);
        else if (a > 0)
            return -div(a, -b);
        else
            return div(-a - b - 1, -b);
    }

    //
    // i = 1,     3,     5,     7,      9, ...
    //     d, d - 1, d - 4, d - 9, d - 16,  
    //
    template<typename num_t>
    static num_t sqrt(num_t d) {
        if (d <= 1)
            return d;
        auto sq = 2*sqrt(div(d, num_t(4))) + 1;
        if (sq * sq <= d)
            return sq;
        return sq - 1;
    }

    //
    // a*x^2 + b*x + c = sum
    // 
    template<typename num_t>
    void arith_base<num_t>::find_quadratic_moves(ineq const& ineq, var_t x, num_t const& a, num_t const& b, num_t const& sum) {
        num_t c, d;
        try {
            c = sum - a * value(x) * value(x) - b * value(x);
            d = b * b - 4 * a * c;
        }
        catch (overflow_exception const&) {
            return;
        }
        if (d < 0)
            return;
        num_t root = sqrt(d);
        bool is_square = root * root == d;
        num_t ll = divide_floor(x, -b - root, 2 * a);
        num_t lh = divide_ceil(x, -b - root, 2 * a);
        num_t rl = divide_floor(x, -b + root, 2 * a);
        num_t rh = divide_ceil(x, -b + root, 2 * a);
        if (lh > rl) {
            std::swap(ll, rl);
            std::swap(lh, rh);
        }
        num_t eps(1);
        if (!is_int(x) &&  abs(rh - lh) <= eps)
            eps = abs(rh - lh) / num_t(2);
        SASSERT(ll <= lh && ll + 1 >= lh);
        SASSERT(rl <= rh && rl + 1 >= rh);
        SASSERT(!is_square || ll != lh || a * ll * ll + b * ll + c == 0);
        SASSERT(!is_square || rl != rh || a * rl * rl + b * rl + c == 0);
        if (d > 0 && lh == rh)
            return;
        if (d == 0 && ll != lh)
            return;

        if (ineq.is_true()) {
            switch (ineq.m_op) {
            case ineq_kind::LE:
                SASSERT(sum <= 0);
                if (d == 0)
                    break;
                if (a < 0) {
                    if (a * lh * lh + b * lh + c <= 0)
                        lh += eps;
                    if (a * rl * rl + b * rl + c <= 0)
                        rl -= eps;
                    SASSERT(!is_square || a * lh * lh + b * lh + c > 0);
                    SASSERT(!is_square || a * rl * rl + b * rl + c > 0);
                    add_update(x, lh - value(x));
                    add_update(x, rl - value(x));
                }
                else {
                    if (a * ll * ll + b * ll + c <= 0)
                        ll -= eps;
                    if (a * rh * rh + b * rh + c <= 0)
                        rh += eps;
                    SASSERT(!is_square || a * ll * ll + b * ll + c > 0);
                    SASSERT(!is_square || a * rh * rh + b * rh + c > 0);
                    add_update(x, ll - value(x));
                    add_update(x, rh - value(x));
                }
                break;
            case ineq_kind::LT: 
                SASSERT(sum < 0);
                SASSERT(!is_int(x));
                SASSERT(ll == lh);
                SASSERT(rl == rh);
                if (d == 0)
                    break;

                if (a > 0) {
                    SASSERT(!is_square || a * (ll + eps) * (ll + eps) + b * (ll + eps) + c >= 0);
                    SASSERT(!is_square || a * (rl - eps) * (rl - eps) + b * (rl - eps) + c >= 0);
                    add_update(x, lh - value(x) + eps);
                    if (ll != rl)
                        add_update(x, rh - value(x) - eps);
                }
                else {
                    SASSERT(!is_square || a * (ll - eps) * (ll - eps) + b * (ll - eps) + c >= 0);
                    SASSERT(!is_square || a * (rl + eps) * (rl + eps) + b * (rl + eps) + c >= 0);
                    add_update(x, ll - value(x) - eps);
                    if (ll != rl)
                        add_update(x, rl - value(x) + eps);
                }
                break;            
            case ineq_kind::EQ:
                SASSERT(sum == 0);
                SASSERT(!is_square || a * (value(x) + 1) * (value(x) + 1) + b * (value(x) + 1) + c != 0);
                SASSERT(!is_square || a * (value(x) - 1) * (value(x) - 1) + b * (value(x) - 1) + c != 0);
                add_update(x, num_t(1) - value(x));
                add_update(x, num_t(-1) - value(x));
                break;
            }
        }
        else {
            switch (ineq.m_op) {
            case ineq_kind::LE:
                SASSERT(sum > 0);
                if (d == 0) {
                    SASSERT(!is_square || !is_int(x) || a <= 0 || ll != lh || a * ll * ll + b * ll + c <= 0);
                    if (a > 0 && ll == lh)
                        add_update(x, ll - value(x));
                    break;
                }
                SASSERT(d > 0);
                if (a > 0) {
                    if (a * lh * lh + b * lh + c > 0)
                        lh += eps;
                    if (a * rl * rl + b * rl + c > 0)
                        rl -= eps;
                    SASSERT(!is_square || a * lh * lh + b * lh + c <= 0);
                    SASSERT(!is_square || a * rl * rl + b * rl + c <= 0);
                    add_update(x, lh - value(x));
                    add_update(x, rl - value(x));
                }
                else {
                    if (a * ll * ll + b * ll + c > 0)
                        ll += eps;
                    if (a * rh * rh + b * rh + c > 0)
                        rh -= eps;
                    SASSERT(!is_square || a * ll * ll + b * ll + c <= 0);
                    SASSERT(!is_square || a * rh * rh + b * rh + c <= 0);
                    add_update(x, ll - value(x));
                    add_update(x, rh - value(x));
                }
                break;
            case ineq_kind::LT:                    
                SASSERT(sum >= 0);
                SASSERT(!is_int(x));
                if (d == 0)
                    break;
                SASSERT(d > 0);
                if (a > 0) {
                    SASSERT(!is_square || a * (ll - eps) * (ll - eps) + b * (ll - eps) + c < 0);
                    SASSERT(!is_square || a * (rl + eps) * (rl + eps) + b * (rl + eps) + c < 0);
                    add_update(x, lh - value(x) - eps);
                    if (ll != rl)
                        add_update(x, rh - value(x) + eps);
                }
                else {
                    SASSERT(!is_square || a* (ll + eps)* (ll + eps) + b * (ll + eps) + c < 0);
                    SASSERT(!is_square || a* (rl - eps)* (rl - eps) + b * (rl - eps) + c < 0);
                    add_update(x, ll - value(x) + eps);
                    if (ll != rl)
                        add_update(x, rl - value(x) - eps);
                }
                break;            
            case ineq_kind::EQ:
                SASSERT(sum != 0);
                if (!is_square)
                    break;
                if (ll == lh) 
                    add_update(x, ll - value(x));
                if (rl == rh && lh != rh)
                    add_update(x, rl - value(x));                
                break;
            }
        }
    }

    template<typename num_t>
    void arith_base<num_t>::find_linear_moves(ineq const& ineq, var_t v, num_t const& coeff, num_t const& sum) {
        if (ineq.is_true()) {
            switch (ineq.m_op) {
            case ineq_kind::LE:
                SASSERT(sum <= 0);
                add_update(v, divide(v, -sum + 1, coeff));
                break;
            case ineq_kind::LT:
                SASSERT(sum < 0);
                add_update(v, divide(v, -sum, coeff));
                break;
            case ineq_kind::EQ: {
                SASSERT(sum == 0);
                add_update(v, num_t(1));
                add_update(v, num_t(- 1));
                break;
            }
            default:
                UNREACHABLE();
                break;
            }
        }
        else {
            switch (ineq.m_op) {
            case ineq_kind::LE:
                SASSERT(sum > 0);
                add_update(v, - divide(v, sum, coeff));
                break;
            case ineq_kind::LT:
                SASSERT(sum >= 0);
                add_update(v, - divide(v, sum + 1, coeff));
                break;
            case ineq_kind::EQ: {
                num_t delta = sum;
                SASSERT(sum != 0);
                delta = sum < 0 ? divide(v, abs(sum), coeff) : -divide(v, sum, coeff);
                if (sum + coeff * delta == 0)
                    add_update(v, delta);
                break;
            }
            default:
                UNREACHABLE();
                break;
            }
        }
    }

    template<typename num_t>
    bool arith_base<num_t>::is_permitted_update(var_t v, num_t const& delta, num_t & delta_out) {
        auto& vi = m_vars[v];

        delta_out = delta;

        if (m_last_var == v && m_last_delta == -delta) 
            return false;        

        if (m_use_tabu && vi.is_tabu(m_stats.m_num_steps, delta)) 
            return false;
        

        auto old_value = value(v);
        auto new_value = old_value + delta;
        if (!vi.in_range(new_value)) 
            return false;        


        if (m_use_tabu && !in_bounds(v, new_value) && in_bounds(v, old_value)) {
            auto const& lo = m_vars[v].m_lo;
            auto const& hi = m_vars[v].m_hi;
            if (lo && (lo->is_strict ? lo->value >= new_value : lo->value > new_value)) {
                if (lo->is_strict && delta_out < 0 && lo->value <= old_value) {
                    num_t eps(1);
                    if (hi && hi->value - lo->value <= eps)
                        eps = (hi->value - lo->value) / num_t(2);
                    delta_out = lo->value - old_value + eps;
                }
                else if (!lo->is_strict && delta_out < 0 && lo->value < old_value)
                    delta_out = lo->value - old_value;
                else
                    return false;
            }
            if (hi && (hi->is_strict ? hi->value <= new_value : hi->value < new_value)) {
                if (hi->is_strict && delta_out >= 0 && hi->value >= old_value) {
                    num_t eps(1);
                    if (lo && hi->value - lo->value <= eps)
                        eps = (hi->value - lo->value) / num_t(2);
                    delta_out = hi->value - old_value - eps;
                }
                else if (!hi->is_strict && delta_out > 0 && hi->value > old_value)
                    delta_out = hi->value - old_value;
                else
                    return false;
            }
        }
        return delta_out != 0;
    }

    template<typename num_t>
    void arith_base<num_t>::add_update(var_t v, num_t delta) { 
        num_t delta_out;
        if (!is_permitted_update(v, delta, delta_out)) 
            return;        
        m_updates.push_back({ v, delta_out, 0 }); 
    }

    // flip on the first positive score
    // it could be changed to flip on maximal positive score
    // or flip on maximal non-negative score
    // or flip on first non-negative score

    // prefer maximal score
    // prefer v/delta with oldest occurrence with same direction
    // 

    template<typename num_t>
    bool arith_base<num_t>::apply_update() {

        while (m_updates.size() > m_updates_max_size) {
            auto idx = ctx.rand(m_updates.size());
            m_updates[idx] = m_updates.back();
            m_updates.pop_back();
        }

        for (auto & [v, delta, score] : m_updates)
            score = compute_score(v, delta);

        double sum_score = 0;

        for (auto const& [v, delta, score] : m_updates)
            sum_score += score;

        while (!m_updates.empty()) {

            unsigned i = m_updates.size();
            double lim = sum_score * ((double)ctx.rand() / random_gen().max_value());
            do {
                lim -= m_updates[--i].m_score;
            } while (lim >= 0 && i > 0);

            auto [v, delta, score] = m_updates[i];

            num_t new_value = value(v) + delta;


            if (update(v, new_value)) {
                m_last_delta = delta;
                m_stats.m_num_steps++;
                m_vars[v].set_step(m_stats.m_num_steps, m_stats.m_num_steps + 3 + ctx.rand(10), delta);
                return true;
            }
            sum_score -= score;
            m_updates[i] = m_updates.back();
            m_updates.pop_back();
        }
        return false;
    }

    template<typename num_t>
    bool arith_base<num_t>::find_lin_moves(sat::literal lit) {
        m_updates.reset();
        auto* ineq = get_ineq(lit.var());
        num_t a, b;
        if (!ineq)
            return false;
        if (!ineq->m_is_linear) {
            for (auto const& [coeff, x] : ineq->m_args) {
                if (is_fixed(x))
                    continue;
                find_linear_moves(*ineq, x, coeff, ineq->m_args_value);
            }
        }
        return apply_update();
    }

    template<typename num_t>
    bool arith_base<num_t>::repair(sat::literal lit) {
        
        m_last_literal = lit;
        if (find_nl_moves(lit))
            return true;

        flet<bool> _tabu(m_use_tabu, false);
        if (false && find_nl_moves(lit))
            return true;
        if (false && find_lin_moves(lit))
            return true;
        return find_reset_moves(lit);
    }

    template<typename num_t>
    num_t arith_base<num_t>::compute_dts(unsigned cl) const {
        num_t d(1), d2;
        bool first = true;
        for (auto a : ctx.get_clause(cl)) {
            auto const* ineq = get_ineq(a.var());
            if (!ineq)
                continue;
            d2 = dtt(a.sign(), *ineq);
            if (first)
                d = d2, first = false;
            else
                d = std::min(d, d2);
            if (d == 0)
                break;
        }
        return d;
    }

    template<typename num_t>
    num_t arith_base<num_t>::dts(unsigned cl, var_t v, num_t const& new_value) const {
        num_t d(1), d2;
        bool first = true;
        for (auto lit : ctx.get_clause(cl)) {
            auto const* ineq = get_ineq(lit.var());
            if (!ineq)
                continue;
            d2 = dtt(lit.sign(), *ineq, v, new_value);
            if (first)
                d = d2, first = false;
            else
                d = std::min(d, d2);
            if (d == 0)
                break;
        }
        return d;
    }


    template<typename num_t>
    bool arith_base<num_t>::in_bounds(var_t v, num_t const& value) {
        auto const& vi = m_vars[v];
        auto const& lo = vi.m_lo;
        auto const& hi = vi.m_hi;
        if (lo && value < lo->value)
            return false;
        if (lo && lo->is_strict && value <= lo->value)
            return false;
        if (hi && value > hi->value)
            return false;
        if (hi && hi->is_strict && value >= hi->value)
            return false;
        return true;
    }

    template<typename num_t>
    bool arith_base<num_t>::is_fixed(var_t v) {
        auto const& vi = m_vars[v];
        auto const& lo = vi.m_lo;
        auto const& hi = vi.m_hi;
        return lo && hi && lo->value == hi->value && lo->value == value(v);
    }

    template<typename num_t>
    bool arith_base<num_t>::update(var_t v, num_t const& new_value) {
        auto& vi = m_vars[v];
        expr* e = vi.m_expr;
        auto old_value = vi.value();
        if (old_value == new_value)
            return true;                   
        if (!vi.in_range(new_value))
            return false;
        if (!in_bounds(v, new_value) && in_bounds(v, old_value))
            return false;

        // check for overflow
        try {
            for (auto idx : vi.m_muls) {
                auto const& [w, monomial] = m_muls[idx];
                num_t prod(1);
                for (auto [w, p] : monomial)
                    prod *= power_of(v == w ? new_value : value(w), p);
            }
        }
        catch (overflow_exception const&) {
            verbose_stream() << "overflow1\n";
            return false;
        }

        buffer<sat::bool_var> to_flip;
        for (auto const& [coeff, bv] : vi.m_ineqs) {
            auto& ineq = *get_ineq(bv);
            bool old_sign = sign(bv);
            sat::literal lit(bv, old_sign);
            SASSERT(ctx.is_true(lit));
            ineq.m_args_value += coeff * (new_value - old_value);
            num_t dtt_new = dtt(old_sign, ineq);
            if (dtt_new != 0)
                to_flip.push_back(bv);
            
        }
        IF_VERBOSE(5, verbose_stream() << "repair: v" << v << " := " << old_value << " -> " << new_value << "\n");
        vi.set_value(new_value);
        ctx.new_value_eh(e);
        m_last_var = v;

        for (auto bv : to_flip) {
            if (dtt(sign(bv), *get_ineq(bv)) != 0)
                ctx.flip(bv);
            SASSERT(dtt(sign(bv), *get_ineq(bv)) == 0);
        }

        IF_VERBOSE(10, verbose_stream() << "new value eh " << mk_bounded_pp(e, m) << "\n");

        for (auto idx : vi.m_muls)
            ctx.new_value_eh(m_vars[m_muls[idx].m_var].m_expr);
        for (auto idx : vi.m_adds) 
            ctx.new_value_eh(m_vars[m_adds[idx].m_var].m_expr);

        for (auto idx : vi.m_muls) {
            auto const& [w, monomial] = m_muls[idx];
            num_t prod(1);
            try {
                for (auto [w, p] : monomial)
                    prod *= power_of(value(w), p);
            }
            catch (overflow_exception const&) {
                verbose_stream() << "overflow\n";
                return false;
            }
            if (value(w) != prod && !update(w, prod))
                return false;
            
        }

        for (auto idx : vi.m_adds) {
            auto const& ad = m_adds[idx];
            auto w = ad.m_var;
            num_t sum(ad.m_coeff);
            for (auto const& [coeff, w] : ad.m_args)
                sum += coeff * value(w);
            if (!update(ad.m_var, sum)) 
                return false;
        }

        return true;
    }
  
    template<typename num_t>
    typename arith_base<num_t>::ineq& arith_base<num_t>::new_ineq(ineq_kind op, num_t const& coeff) {
        auto* i = alloc(ineq);
        i->m_coeff = coeff;
        i->m_op = op;
        return *i;
    }

    template<typename num_t>
    void arith_base<num_t>::add_arg(linear_term& ineq, num_t const& c, var_t v) {
        if (c != 0)
            ineq.m_args.push_back({ c, v });
    }

    template<>
    bool arith_base<checked_int64<true>>::is_num(expr* e, checked_int64<true>& i) {
        rational r;
        if (a.is_extended_numeral(e, r)) {            
            if (!r.is_int64())
                throw overflow_exception();
            i = r.get_int64();
            return true;
        }
        return false;
    }

    template<>
    bool arith_base<rational>::is_num(expr* e, rational& i) {
        return a.is_extended_numeral(e, i);
    }

    template<typename num_t>
    bool arith_base<num_t>::is_num(expr* e, num_t& i) {
        UNREACHABLE();
        return false;
    }

    template<>
    expr_ref arith_base<rational>::from_num(sort* s, rational const& n) {
        return expr_ref(a.mk_numeral(n, s), m);
    }

    template<>
    expr_ref arith_base<checked_int64<true>>::from_num(sort* s, checked_int64<true> const& n) {
        return expr_ref(a.mk_numeral(rational(n.get_int64(), rational::i64()), s), m);
    }

    template<typename num_t>
    expr_ref arith_base<num_t>::from_num(sort* s, num_t const& n) {
        UNREACHABLE();
        return expr_ref(m);
    }

    template<typename num_t>
    void arith_base<num_t>::add_args(linear_term& term, expr* e, num_t const& coeff) {
        auto v = m_expr2var.get(e->get_id(), UINT_MAX);
        expr* x, * y;
        num_t i;
        if (v != UINT_MAX)
            add_arg(term, coeff, v);
        else if (is_num(e, i))
            term.m_coeff += coeff * i;
        else if (a.is_add(e)) {
            for (expr* arg : *to_app(e))
                add_args(term, arg, coeff);
        }
        else if (a.is_sub(e, x, y)) {
            add_args(term, x, coeff);
            add_args(term, y, -coeff);
        }
        else if (a.is_mul(e, x, y) && is_num(x, i)) {
            add_args(term, y, i * coeff);
        }
        else if (a.is_mul(e)) {
            unsigned_vector ms;
            for (expr* arg : *to_app(e)) 
                ms.push_back(mk_term(arg));            

            switch (ms.size()) {
            case 0:
                term.m_coeff += coeff;
                break;
            case 1:
                add_arg(term, coeff, ms[0]);
                break;
            default: {
                v = mk_var(e);
                unsigned idx = m_muls.size();
                std::stable_sort(ms.begin(), ms.end(), [&](unsigned a, unsigned b) { return a < b; });
                svector<std::pair<unsigned, unsigned>> mp;
                for (unsigned i = 0; i < ms.size(); ++i) {
                    auto w = ms[i];
                    auto p = 1;
                    while (i + 1 < ms.size() && ms[i + 1] == w)
                        ++p, ++i;
                    mp.push_back({ w, p });
                }
                m_muls.push_back({ v, mp });
                num_t prod(1);
                for (auto [w, p] : mp)
                    m_vars[w].m_muls.push_back(idx), prod *= power_of(value(w), p);
                m_vars[v].m_def_idx = idx;
                m_vars[v].m_op = arith_op_kind::OP_MUL;
                m_vars[v].set_value(prod);
                add_arg(term, coeff, v);
                break;
            }
            }
        }
        else if (a.is_uminus(e, x))
            add_args(term, x, -coeff);
        else if (a.is_mod(e, x, y) || a.is_mod0(e, x, y))
            add_arg(term, coeff, mk_op(arith_op_kind::OP_MOD, e, x, y));
        else if (a.is_idiv(e, x, y) || a.is_idiv0(e, x, y))
            add_arg(term, coeff, mk_op(arith_op_kind::OP_IDIV, e, x, y));
        else if (a.is_div(e, x, y) || a.is_div0(e, x, y))
            add_arg(term, coeff, mk_op(arith_op_kind::OP_DIV, e, x, y));
        else if (a.is_rem(e, x, y))
            add_arg(term, coeff, mk_op(arith_op_kind::OP_REM, e, x, y));
        else if (a.is_power(e, x, y) || a.is_power0(e, x, y))
            add_arg(term, coeff, mk_op(arith_op_kind::OP_POWER, e, x, y));
        else if (a.is_abs(e, x))
            add_arg(term, coeff, mk_op(arith_op_kind::OP_ABS, e, x, x));
        else if (a.is_to_int(e, x))
            add_arg(term, coeff, mk_op(arith_op_kind::OP_TO_INT, e, x, x));
        else if (a.is_to_real(e, x))
            add_arg(term, coeff, mk_op(arith_op_kind::OP_TO_REAL, e, x, x));       
        else if (a.is_arith_expr(e)) {
            NOT_IMPLEMENTED_YET();
        }
        else 
            add_arg(term, coeff, mk_var(e));
    }

    template<typename num_t>
    typename arith_base<num_t>::var_t arith_base<num_t>::mk_op(arith_op_kind k, expr* e, expr* x, expr* y) {
        auto v = mk_var(e);
        auto vx = mk_term(x);
        auto vy = mk_term(y);
        unsigned idx = m_ops.size();
        num_t val;
        switch (k) {
        case arith_op_kind::OP_MOD:
            val = value(vy) == 0 ? num_t(0) : mod(value(v), value(vy));
            break;
        case arith_op_kind::OP_REM:
            if (value(vy) == 0)
                val = 0;
            else {
                val = value(vx);
                val %= value(vy);
            }
            break;
        case arith_op_kind::OP_IDIV:
            val = value(vy) == 0 ? num_t(0): div(value(vx), value(vy));
            break;
        case arith_op_kind::OP_DIV:
            val = value(vy) == 0? num_t(0) : value(vx) / value(vy);
            break;
        case arith_op_kind::OP_ABS:
            val = abs(value(vx));
            break;
        default:
            NOT_IMPLEMENTED_YET();
            break;
        }
        m_ops.push_back({v, k, vx, vy});
        m_vars[v].m_def_idx = idx;
        m_vars[v].m_op = k;
        m_vars[v].set_value(val);
        return v;
    }

    template<typename num_t>
    typename arith_base<num_t>::var_t arith_base<num_t>::mk_term(expr* e) {
        auto v = m_expr2var.get(e->get_id(), UINT_MAX);
        if (v != UINT_MAX)
            return v;
        linear_term t;
        add_args(t, e, num_t(1));
        if (t.m_coeff == 0 && t.m_args.size() == 1 && t.m_args[0].first == 1)
            return t.m_args[0].second;
        v = mk_var(e);
        auto idx = m_adds.size();
        num_t sum(t.m_coeff);
        m_adds.push_back({ { t.m_args, t.m_coeff }, v });
        for (auto const& [c, w] : t.m_args)
            m_vars[w].m_adds.push_back(idx), sum += c * value(w);
        m_vars[v].m_def_idx = idx;
        m_vars[v].m_op = arith_op_kind::OP_ADD;
        m_vars[v].set_value(sum);
        return v;
    }

    template<typename num_t>
    typename arith_base<num_t>::var_t arith_base<num_t>::mk_var(expr* e) {
        var_t v = m_expr2var.get(e->get_id(), UINT_MAX);
        if (v == UINT_MAX) {
            v = m_vars.size();
            m_expr2var.setx(e->get_id(), v, UINT_MAX);
            m_vars.push_back(var_info(e, a.is_int(e) ? var_sort::INT : var_sort::REAL));     
        }
        return v;
    }

    template<typename num_t>
    void arith_base<num_t>::init_bool_var(sat::bool_var bv) {
        expr* e = ctx.atom(bv);
        if (m_ineqs.get(bv, nullptr))
            return;
        if (!e)
            return;
        expr* x, * y;
        m_ineqs.reserve(bv + 1);
        if (a.is_le(e, x, y) || a.is_ge(e, y, x)) {
            auto& ineq = new_ineq(ineq_kind::LE, num_t(0));
            add_args(ineq, x, num_t(1));
            add_args(ineq, y, num_t(-1));
            init_ineq(bv, ineq);
        }
        else if ((a.is_lt(e, x, y) || a.is_gt(e, y, x)) && a.is_int(x)) {
            auto& ineq = new_ineq(ineq_kind::LE, num_t(1));
            add_args(ineq, x, num_t(1));
            add_args(ineq, y, num_t(-1));
            init_ineq(bv, ineq);
        }
        else if ((a.is_lt(e, x, y) || a.is_gt(e, y, x)) && a.is_real(x)) {
            auto& ineq = new_ineq(ineq_kind::LT, num_t(0));
            add_args(ineq, x, num_t(1));
            add_args(ineq, y, num_t(-1));
            init_ineq(bv, ineq);
        }
        else if (m.is_eq(e, x, y) && a.is_int_real(x)) {
            auto& ineq = new_ineq(ineq_kind::EQ, num_t(0));
            add_args(ineq, x, num_t(1));
            add_args(ineq, y, num_t(-1));
            init_ineq(bv, ineq);
        }
        else if (is_distinct(e)) {
            verbose_stream() << "distinct " << mk_pp(e, m) << "\n";
        }
        else if (a.is_is_int(e, x))
        {
            NOT_IMPLEMENTED_YET();
        }
#if 0
        else if (a.is_idivides(e, x, y))
            NOT_IMPLEMENTED_YET();
#endif
        else {
            SASSERT(!a.is_arith_expr(e));
        }
        
    }

    template<typename num_t>
    void arith_base<num_t>::init_ineq(sat::bool_var bv, ineq& i) {

        // ensure that variables are unique in the linear term:
        std::stable_sort(i.m_args.begin(), i.m_args.end(), [&](auto const& a, auto const& b) { return a.second < b.second; });
        unsigned k = 0;
        for (unsigned j = 0; j < i.m_args.size(); ++j) {
            if (j > k && i.m_args[k].second == i.m_args[j].second) 
                i.m_args[k].first += i.m_args[j].first;            
            else
                i.m_args[k++] = i.m_args[j];
        }
        i.m_args.shrink(k);
        i.m_monomials.reserve(k);
        for (unsigned j = 0; j < i.m_args.size(); ++j) {
            auto const& [c, v] = i.m_args[j];
            if (is_mul(v))
                i.m_monomials[j].append(get_mul(v).m_monomial);
            else
                i.m_monomials[j].push_back({ v, 1 });
        }
        // compute the value of the linear term, and accumulate non-linear sub-terms
        i.m_args_value = i.m_coeff;
        for (auto const& [coeff, v] : i.m_args) {
            m_vars[v].m_ineqs.push_back({ coeff, bv });
            i.m_args_value += coeff * value(v);
            if (is_mul(v)) {
                auto const& [w, monomial] = get_mul(v);
                for (auto [w, p] : monomial) 
                    i.m_nonlinear.push_back({ w, { {v, coeff, p} } });
                i.m_is_linear = false;
            }
            else
                i.m_nonlinear.push_back({ v, { { v, coeff, 1 } } });
        }
        std::stable_sort(i.m_nonlinear.begin(), i.m_nonlinear.end(), [&](auto const& a, auto const& b) { return a.first < b.first; });

        // ensure that non-linear terms are have a unique summary.
        k = 0;
        for (unsigned j = 0; j < i.m_nonlinear.size(); ++j) {
            if (j > k && i.m_nonlinear[k].first == i.m_nonlinear[j].first) 
                i.m_nonlinear[k].second.append(i.m_nonlinear[j].second);            
            else
                i.m_nonlinear[k++] = i.m_nonlinear[j];
        }
        i.m_nonlinear.shrink(k);

        // Ensure that non-linear term occurrences are sorted, and
        // that terms with the same variable are combined.
        for (auto& [x, nl] : i.m_nonlinear) {
            if (nl.size() == 1)
                continue;
            std::stable_sort(nl.begin(), nl.end(), [&](auto const& a, auto const& b) { return a.p < b.p; });
            k = 0;
            for (unsigned j = 0; j < nl.size(); ++j) {
                if (j > k && nl[k].v == nl[j].v) 
                    nl[k].coeff += nl[j].coeff;
                else
                    nl[k++] = nl[j];
            }
            nl.shrink(k);
        }

        // attach i to bv
        m_ineqs.set(bv, &i);
     }

    template<typename num_t>
    void arith_base<num_t>::init_bool_var_assignment(sat::bool_var v) {
        auto* ineq = get_ineq(v);
        if (ineq && ineq->is_true() != ctx.is_true(v))
            ctx.flip(v);
        if (is_distinct(ctx.atom(v)) && eval_distinct(ctx.atom(v)) != ctx.is_true(v))
            ctx.flip(v);
    }

    template<typename num_t>
    void arith_base<num_t>::propagate_literal(sat::literal lit) {        
        if (!ctx.is_true(lit))
            return;
        expr* e = ctx.atom(lit.var());
        if (is_distinct(e) && eval_distinct(e) != ctx.is_true(lit)) {
            repair_distinct(e);
            return;
        }
        auto const* ineq = get_ineq(lit.var());
        if (!ineq)
            return;      
        if (ineq->is_true() != lit.sign())
            return;
        repair(lit);
    }

    template<typename num_t>
    void arith_base<num_t>::repair_literal(sat::literal lit) {
        init_bool_var_assignment(lit.var());      
    }

    template<typename num_t>
    bool arith_base<num_t>::propagate() {
       // m_last_var = UINT_MAX; // allow to change last variable.
        return false;
    }


    template<typename num_t>
    num_t arith_base<num_t>::value1(var_t v) {
        auto const& vi = m_vars[v];
        if (vi.m_def_idx == UINT_MAX)
            return value(v);

        num_t result, v1, v2;
        switch (vi.m_op) {
        case LAST_ARITH_OP:
            break;
        case OP_ADD: {
            auto const& ad = m_adds[vi.m_def_idx];
            auto const& args = ad.m_args;
            result = ad.m_coeff;
            for (auto [c, w] : args)
                result += c * value(w);
            break;
        }
        case OP_MUL: {
            auto const& [w, monomial] = m_muls[vi.m_def_idx];
            result = num_t(1);
            for (auto [w, p] : monomial)
                result *= power_of(value(w), p);
            break;
        }
        case OP_MOD:
            v1 = value(m_ops[vi.m_def_idx].m_arg1);
            v2 = value(m_ops[vi.m_def_idx].m_arg2);
            result = v2 == 0 ? num_t(0) : mod(v1, v2);
            break;
        case OP_DIV:
            v1 = value(m_ops[vi.m_def_idx].m_arg1);
            v2 = value(m_ops[vi.m_def_idx].m_arg2);
            result = v2 == 0 ? num_t(0) : v1 / v2;
            break;
        case OP_IDIV:
            v1 = value(m_ops[vi.m_def_idx].m_arg1);
            v2 = value(m_ops[vi.m_def_idx].m_arg2);
            result = v2 == 0 ? num_t(0) : div(v1, v2);
            break;
        case OP_REM:
            v1 = value(m_ops[vi.m_def_idx].m_arg1);
            v2 = value(m_ops[vi.m_def_idx].m_arg2);
            result = v2 == 0 ? num_t(0) : v1 %= v2;
            break;
        case OP_ABS:
            result = abs(value(m_ops[vi.m_def_idx].m_arg1));
            break;
        default:
            NOT_IMPLEMENTED_YET();
        }
        return result;
    }

    template<typename num_t>
    void arith_base<num_t>::repair_up(app* e) {        
        if (m.is_bool(e)) {
            auto v = ctx.atom2bool_var(e);
            auto const* ineq = get_ineq(v);
            if (ineq && ineq->is_true() != ctx.is_true(v))
                ctx.flip(v);
            return;
        }
        auto v = m_expr2var.get(e->get_id(), UINT_MAX);
        if (v == UINT_MAX)
            return;
        auto const& vi = m_vars[v];
        if (vi.m_def_idx == UINT_MAX)
            return;
        auto new_value = value1(v);
        if (!update(v, new_value))
            ctx.new_value_eh(e);
    }

    template<typename num_t>
    bool arith_base<num_t>::repair_down(app* e) {
        auto v = m_expr2var.get(e->get_id(), UINT_MAX);
        if (v == UINT_MAX)
            return false;
        auto const& vi = m_vars[v];
        if (vi.m_def_idx == UINT_MAX)
            return false;
        flet<bool> _tabu(m_use_tabu, false);
        TRACE("sls", tout << "repair def " << mk_bounded_pp(vi.m_expr, m) << "\n");
        switch (vi.m_op) {
        case arith_op_kind::LAST_ARITH_OP:
            break;
        case arith_op_kind::OP_ADD:
            return repair_add(m_adds[vi.m_def_idx]);
        case arith_op_kind::OP_MUL:
            return repair_mul(m_muls[vi.m_def_idx]);
        case arith_op_kind::OP_MOD:
            return repair_mod(m_ops[vi.m_def_idx]);
        case arith_op_kind::OP_REM:
            return repair_rem(m_ops[vi.m_def_idx]);
        case arith_op_kind::OP_POWER:
            return repair_power(m_ops[vi.m_def_idx]);
        case arith_op_kind::OP_IDIV:
            return repair_idiv(m_ops[vi.m_def_idx]);
        case arith_op_kind::OP_DIV:
            return repair_div(m_ops[vi.m_def_idx]);
        case arith_op_kind::OP_ABS:
            return repair_abs(m_ops[vi.m_def_idx]);
        case arith_op_kind::OP_TO_INT:
            return repair_to_int(m_ops[vi.m_def_idx]);
        case arith_op_kind::OP_TO_REAL:
            return repair_to_real(m_ops[vi.m_def_idx]);
        default:
            NOT_IMPLEMENTED_YET();
        }
        return true;
    }

    template<typename num_t>
    void arith_base<num_t>::initialize() { 
        for (auto lit : ctx.unit_literals())
            initialize_unit(lit);
        for (unsigned v = 0; v < m_vars.size(); ++v) {
            auto const& vi = m_vars[v];
            if (vi.m_lo || vi.m_hi)
                continue;
            expr* e = vi.m_expr;
            if (is_add(v)) {
                auto const& ad = get_add(v);
                num_t lo(ad.m_coeff), hi(ad.m_coeff);
                bool lo_valid = true, hi_valid = true;
                bool lo_strict = false, hi_strict = false;
                for (auto const& [c, w] : ad.m_args) {
                    if (!lo_valid && !hi_valid)
                        break;
                    auto const& wi = m_vars[w];
                    if (lo_valid) {
                        if (c > 0 && wi.m_lo)
                            lo += c * wi.m_lo->value,
                            lo_strict |= wi.m_lo->is_strict;
                        else if (c < 0 && wi.m_hi)
                            lo += c * wi.m_hi->value,
                            lo_strict |= wi.m_hi->is_strict;
                        else
                            lo_valid = false;
                    }
                    if (hi_valid) {
                        if (c > 0 && wi.m_hi)
                            hi += c * wi.m_hi->value,
                            hi_strict |= wi.m_hi->is_strict;
                        else if (c < 0 && wi.m_lo)
                            hi += c * wi.m_lo->value,
                            hi_strict |= wi.m_lo->is_strict;
                        else
                            hi_valid = false;
                    }
                }
                if (lo_valid) {
                    if (lo_strict)
                        add_gt(v, lo);
                    else
                        add_ge(v, lo);
                }
                if (hi_valid) {
                    if (hi_strict)
                        add_lt(v, hi);
                    else
                        add_le(v, hi);
                }
            }
            if (is_mul(v)) {
                auto const& [w, monomial] = get_mul(v);
                num_t lo(1), hi(1);
                bool lo_valid = true, hi_valid = true;
                bool lo_strict = false, hi_strict = false;
                for (auto [w, p] : monomial) {
                    if (!lo_valid)
                        break;
                    auto const& wi = m_vars[w];
                    if (wi.m_lo && !wi.m_lo->is_strict && wi.m_lo->value >= 0)
                        lo *= power_of(wi.m_lo->value, p);
                    else
                        lo_valid = false;
                }
                for (auto [w, p] : monomial) {
                    if (!lo_valid && !hi_valid)
                        break;
                    auto const& wi = m_vars[w];
                    try {
                        if (wi.m_hi && !wi.m_hi->is_strict)
                            hi *= power_of(wi.m_hi->value, p);
                        else
                            hi_valid = false;
                    }
                    catch (overflow_exception&) {
                        verbose_stream() << "overflow3\n";
                        hi_valid = false;
                    }
                }
                if (lo_valid) {
                    if (lo_strict)
                        add_gt(v, lo);
                    else
                        add_ge(v, lo);
                }
                if (lo_valid && hi_valid) {
                    if (hi_strict)
                        add_lt(v, hi);
                    else
                        add_le(v, hi);
                }
            }
            expr* c, * th, * el;
            if (m.is_ite(e, c, th, el)) {
                auto vth = m_expr2var.get(th->get_id(), UINT_MAX);
                auto vel = m_expr2var.get(el->get_id(), UINT_MAX);
                if (vth == UINT_MAX || vel == UINT_MAX)
                    continue;
                auto const& vith = m_vars[vth];
                auto const& viel = m_vars[vel];
                if (vith.m_lo && viel.m_lo && !vith.m_lo->is_strict && !viel.m_lo->is_strict)
                    add_ge(v, std::min(vith.m_lo->value, viel.m_lo->value));
                if (vith.m_hi && viel.m_hi && !vith.m_hi->is_strict && !viel.m_hi->is_strict)
                    add_le(v, std::max(vith.m_hi->value, viel.m_hi->value));

            }
            switch (vi.m_op) {
            case LAST_ARITH_OP:
            case OP_ADD: 
            case OP_MUL: 
                break;
            case OP_MOD: {
                auto v2 = m_ops[vi.m_def_idx].m_arg2;
                auto const& vi2 = m_vars[v2];
                if (vi2.m_lo && vi2.m_hi && vi2.m_lo->value == vi2.m_hi->value && vi2.m_lo->value > 0) {
                    add_le(v, vi2.m_lo->value - 1);
                    add_ge(v, num_t(0));
                }
                break;
            }
            case OP_DIV:
                break;
            case OP_IDIV:
                break;
            case OP_REM:
                break;
            case OP_ABS:
                add_ge(v, num_t(0));
                break;
            default:
                NOT_IMPLEMENTED_YET();

            }
            // TBD: can also do with other operators.
        }
    }

    template<typename num_t>
    void arith_base<num_t>::initialize_unit(sat::literal lit) {
        init_bool_var(lit.var());
        auto* ineq = get_ineq(lit.var());
        if (!ineq)
            return;

        if (ineq->m_args.size() != 1)
            return;
        auto [c, v] = ineq->m_args[0];        
        
        switch (ineq->m_op) {
            case ineq_kind::LE:
                if (lit.sign()) {
                    if (c == -1) // -x + c >= 0 <=> c >= x
                        add_le(v, ineq->m_coeff);
                    else if (c == 1) // x + c >= 0 <=> x >= -c
                        add_ge(v, -ineq->m_coeff);
                    else
                        verbose_stream() << "INITIALIZE " << lit << " " << *ineq << "\n";
                }
                else {
                    if (c == -1)
                        add_ge(v, ineq->m_coeff);
                    else if (c == 1)
                        add_le(v, -ineq->m_coeff);
                    else
                        verbose_stream() << "INITIALIZE " << lit << " " << *ineq << "\n";
                }
                break;
            case ineq_kind::EQ:
                if (!lit.sign()) {
                    if (c == -1) {
                        add_ge(v, ineq->m_coeff);
                        add_le(v, ineq->m_coeff);
                    }
                    else if (c == 1) {
                        add_ge(v, -ineq->m_coeff);
                        add_le(v, -ineq->m_coeff);
                    }
                    else
                        verbose_stream() << "INITIALIZE " << lit << " " << *ineq << "\n";
                }
                break;
            case ineq_kind::LT:

                if (lit.sign()) {
                    if (c == -1) // -x + c >= 0 <=> c >= x
                        add_le(v, ineq->m_coeff);
                    else if (c == 1) // x + c >= 0 <=> x >= -c
                        add_ge(v, -ineq->m_coeff);
                    else
                        verbose_stream() << "INITIALIZE " << lit << " " << *ineq << "\n";
                }
                else {
                    if (c == -1)
                        add_gt(v, ineq->m_coeff);
                    else if (c == 1)
                        add_lt(v, -ineq->m_coeff);
                    else
                        verbose_stream() << "INITIALIZE " << lit << " " << *ineq << "\n";
                }
                break;
        }
    }

    template<typename num_t>
    void arith_base<num_t>::add_le(var_t v, num_t const& n) {
        if (m_vars[v].m_hi && m_vars[v].m_hi->value <= n)
            return;
        m_vars[v].m_hi = { false, n };
    }

    template<typename num_t>
    void arith_base<num_t>::add_ge(var_t v, num_t const& n) {
        if (m_vars[v].m_lo && m_vars[v].m_lo->value >= n)
            return;
        m_vars[v].m_lo = { false, n };
    }

    template<typename num_t>
    void arith_base<num_t>::add_lt(var_t v, num_t const& n) {
        if (is_int(v))
            add_le(v, n - 1);
        else
            m_vars[v].m_hi = { true, n };
    }

    template<typename num_t>
    void arith_base<num_t>::add_gt(var_t v, num_t const& n) {
        if (is_int(v))
            add_ge(v, n + 1);
        else 
            m_vars[v].m_lo = { true, n };
    }

    template<typename num_t>
    bool arith_base<num_t>::repair_add(add_def const& ad) {
        auto v = ad.m_var;
        auto old_value = value(v);
        auto const& coeffs = ad.m_args;
        num_t sum(ad.m_coeff);

        for (auto const& [c, w] : coeffs)
            sum += c * value(w);

        if (old_value == sum)
            return true;


        m_updates.reset();

        for (auto const& [coeff, w] : coeffs) {
            auto delta = divide(w, sum - old_value, coeff);
            if (sum == coeff*delta + old_value)
                add_update(w, delta);
        }
        if (apply_update())
            return eval_is_correct(v);

        flet<bool> _use_tabu(m_use_tabu, false);

        m_updates.reset();
        for (auto const& [coeff, w] : coeffs) {
            auto delta = divide(w, sum - old_value, coeff);
            if (sum != coeff*delta + old_value)
                add_update(w, delta);
        }
        for (auto const& [coeff, w] : coeffs)
            add_reset_update(w);    

        if (apply_update())
            return eval_is_correct(v);

        return update(v, sum);
    }

    template<typename num_t>
    bool arith_base<num_t>::repair_mul(mul_def const& md) {
        auto const& [v, monomial] = md;
        num_t product(1);
        num_t val = value(v);
        for (auto [v, p]: monomial)
            product *= power_of(value(v), p);
        if (product == val)
            return true;
        IF_VERBOSE(10, verbose_stream() << "v" << v << " repair mul " << mk_bounded_pp(m_vars[v].m_expr, m) << " : = " << val << " (product : " << product << ")\n");

        
        m_updates.reset();
        if (val == 0) {
            for (auto [x, p] : monomial)
                add_update(x, -value(x));
        }
        else if (val == 1 || val == -1) {
            for (auto [x, p] : monomial) {
                add_update(x, num_t(1) - value(x));                
                add_update(x, num_t(-1) - value(x));
            }
        }
        else {
            for (auto [x, p] : monomial) {
                auto mx = mul_value_without(v, x);
                // val / mx = x^p
                if (mx == 0)
                    continue;
                auto valmx = divide(x, val, mx);
                auto r = root_of(p, valmx);
                add_update(x, r - value(x));
                if (p % 2 == 0) 
                    add_update(x, -r - value(x));
            }
        }

        if (apply_update())
            return eval_is_correct(v);

        flet<bool> _use_tabu(m_use_tabu, false);
        m_updates.reset();
        for (auto [x, p] : monomial)
            add_reset_update(x);

        if (apply_update())
            return eval_is_correct(v);

        return update(v, product); 
    }    

    template<typename num_t>
    bool arith_base<num_t>::repair_rem(op_def const& od) {
        auto v1 = value(od.m_arg1);
        auto v2 = value(od.m_arg2);
        if (v2 == 0) 
            return update(od.m_var, num_t(0));
        

        IF_VERBOSE(0, verbose_stream() << "todo repair rem");
        // bail
        v1 %= v2;
        return update(od.m_var, v1);
    }

    template<typename num_t>
    bool arith_base<num_t>::repair_abs(op_def const& od) {
        auto val = value(od.m_var);
        auto v1 = value(od.m_arg1);
        if (val < 0)
            return update(od.m_var, abs(v1));
        else if (ctx.rand(2) == 0)
            return update(od.m_arg1, val);
        else
            return update(od.m_arg1, -val);        
    }

    template<typename num_t>
    bool arith_base<num_t>::repair_to_int(op_def const& od) {
        auto val = value(od.m_var);
        auto v1 = value(od.m_arg1);
        if (val - 1 < v1 && v1 <= val)
            return true;
        return update(od.m_arg1, val);        
    }

    template<typename num_t>
    bool arith_base<num_t>::repair_to_real(op_def const& od) {
        if (ctx.rand(20) == 0)
            return update(od.m_var, value(od.m_arg1));
        else 
            return update(od.m_arg1, value(od.m_arg1));
    }

    template<typename num_t>
    bool arith_base<num_t>::repair_power(op_def const& od) {
        auto v1 = value(od.m_arg1);
        auto v2 = value(od.m_arg2);
        if (v1 == 0 && v2 == 0) {
            return update(od.m_var, num_t(0));
        }
        IF_VERBOSE(0, verbose_stream() << "todo repair ^");
        NOT_IMPLEMENTED_YET();
        return false;
    }

    template<typename num_t>
    bool arith_base<num_t>::repair_mod(op_def const& od) {        
        auto val = value(od.m_var);
        auto v1 = value(od.m_arg1);
        auto v2 = value(od.m_arg2);
        // repair first argument
        if (val >= 0 && val < v2) {
            auto v3 = mod(v1, v2);
            if (v3 == val)
                return true;
            // find r, such that mod(v1 + r, v2) = val
            // v1 := v1 + val - v3 (+/- v2)
            v1 += val - v3;
            switch (ctx.rand(6)) {
            case 0:
                v1 += v2;
                break;
            case 1:
                v1 -= v2;
                break;
            default:
                break;
            }
            return update(od.m_arg1, v1);
        }
        return update(od.m_var, v2 == 0 ? num_t(0) : mod(v1, v2));
    }

    template<typename num_t>
    bool arith_base<num_t>::repair_idiv(op_def const& od) {
        auto v1 = value(od.m_arg1);
        auto v2 = value(od.m_arg2);
        IF_VERBOSE(0, verbose_stream() << "TODO repair div");
        // bail
        return update(od.m_var, v2 == 0 ? num_t(0) : div(v1, v2));
    }
    
    template<typename num_t>
    bool arith_base<num_t>::repair_div(op_def const& od) {
        auto v1 = value(od.m_arg1);
        auto v2 = value(od.m_arg2);
        IF_VERBOSE(0, verbose_stream() << "TODO repair /");
        // bail
        return update(od.m_var, v2 == 0 ? num_t(0) : v1 / v2);
    }

    template<typename num_t>
    double arith_base<num_t>::compute_score(var_t x, num_t const& delta) {
        int result = 0;
        int breaks = 0;
        for (auto const& [coeff, bv] : m_vars[x].m_ineqs) {
            bool old_sign = sign(bv);
            auto lit = sat::literal(bv, old_sign);
            auto dtt_old = dtt(old_sign, *get_ineq(bv));
            auto dtt_new = dtt(old_sign, *get_ineq(bv), coeff, delta);
#if 1
            if (dtt_new == 0 && dtt_old != 0) 
                result += 1;
            
            if (dtt_new != 0 && dtt_old == 0) {
                if (m_use_tabu && ctx.is_unit(lit))
                    return 0;
                result -= 1;
                breaks += 1;
            }
#else
            if (dtt_new == dtt_old)
                continue;
            if (m_use_tabu && ctx.is_unit(lit) && dtt_new != 0)
                return 0;
            double reward = ctx.reward(bv);
            result += reward;
#endif
        }

        if (result < 0)
            return 0.1;            
        else if (result == 0)
            return 0.2;        
        for (int i = m_prob_break.size(); i <= breaks; ++i) 
            m_prob_break.push_back(std::pow(m_config.cb, -i));
        return m_prob_break[breaks];
    }

    template<typename num_t>
    num_t arith_base<num_t>::mul_value_without(var_t m, var_t x) {
        auto const& vi = m_vars[m];
        auto const& [w, monomial] = m_muls[vi.m_def_idx];
        SASSERT(m == w);
        num_t r(1);
        for (auto [y, p] : monomial)
            if (x != y)
                r *= power_of(value(y), p);
        return r;
    }

    template<typename num_t>
    bool arith_base<num_t>::is_linear(var_t x, vector<nonlinear_coeff> const& nl, num_t& b) {
        if (nl.size() == 1 && nl[0].v == x) {
            b = nl[0].coeff;
            return true;
        }
        b = 0;
        for (auto const& [v, c, p] : nl) {
            if (p > 1)
                return false;
            if (x == v)
                b += c;
            else
                b += c * mul_value_without(v, x);
        }
        return b != 0;
    }

    template<typename num_t>
    bool arith_base<num_t>::is_quadratic(var_t x, vector<nonlinear_coeff> const& nl, num_t& a, num_t& b) {
        a = 0;
        b = 0;
        for (auto const& [v, c, p] : nl) {
            if (p == 1) {
                if (x == v)
                    b += c;                
                else 
                    b += c * mul_value_without(v, x);                
            }
            else if (p == 2) {
                SASSERT(v != x);
                a += c * mul_value_without(v, x);
            }
            else
                return false;
        }
        return a != 0 || b != 0;
    }

    template<typename num_t>
    bool arith_base<num_t>::find_nl_moves(sat::literal lit) {
        m_updates.reset();
        auto* ineq = get_ineq(lit.var());
        num_t a, b;
        if (!ineq)
            return false;
        for (auto const& [x, nl] : ineq->m_nonlinear) {
            if (is_fixed(x))
                continue;
            if (is_linear(x, nl, b))
                find_linear_moves(*ineq, x, b, ineq->m_args_value);
            else if (is_quadratic(x, nl, a, b))
                find_quadratic_moves(*ineq, x, a, b, ineq->m_args_value);
            else
                ;
        }        
        return apply_update();
    }

    template<typename num_t>
    void arith_base<num_t>::add_reset_update(var_t x) {
        m_last_delta = 0;
        if (is_fixed(x))
            return;
        if (is_mul(x)) {
            auto const& [w1, monomial] = get_mul(x);
            for (auto [w1, p] : monomial)
                add_reset_update(w1);
        }
        if (is_add(x)) {
            auto const& ad = get_add(x);
            for (auto [c, w] : ad.m_args)
                add_reset_update(w);
        }
        auto const& vi = m_vars[x];
        auto const& lo = vi.m_lo;
        auto const& hi = vi.m_hi;
        auto new_value = num_t(-2 + (int)ctx.rand(5));
        if (lo && lo->value > new_value)
            new_value = lo->value + num_t(ctx.rand(2));
        else if (hi && hi->value < new_value)
            new_value = hi->value - num_t(ctx.rand(2));
        if (new_value != value(x))
            add_update(x, new_value - value(x) + num_t(-1 + (int)ctx.rand(3)));
        else {
            add_update(x, num_t(1) - value(x));
            add_update(x, -num_t(1) - value(x));
            if (value(x) != 0) {
                add_update(x, num_t(1));
                add_update(x, -num_t(1));
            }
        }
    }

    template<typename num_t>
    bool arith_base<num_t>::find_reset_moves(sat::literal lit) {
        m_updates.reset();
        auto* ineq = get_ineq(lit.var());        
        num_t a, b;
        if (!ineq)
            return false;
        for (auto const& [x, nl] : ineq->m_nonlinear) 
            add_reset_update(x);
        
        IF_VERBOSE(10,
            if (m_updates.empty()) {
                verbose_stream() << lit << ": " << * ineq << "\n";
                for (auto const& [x, nl] : ineq->m_nonlinear) {
                    display(verbose_stream(), x) << "\n";
                }
            }
            verbose_stream() << "RESET moves num updates: " << lit << " " << m_updates.size() << "\n");

        return apply_update();
    }

    template<typename num_t>
    num_t arith_base<num_t>::power_of(num_t x, unsigned k) {
        num_t r(1);
        while (k > 1) {
            if (k % 2 == 1) {
                r = x * r;
                --k;
            }
            x = x * x;
            k /= 2;
        }
        return x * r;
    }

    // Newton function for integer n'th root of a
    // x_{k+1} = 1/k ((k-1)*x_k + a / x_k^{n-1})
    template<typename num_t>
    num_t arith_base<num_t>::root_of(unsigned k, num_t a) {
        if (a <= 1)
            return a;
        if (k == 1)
            return a;
        if (a <= k)
            return num_t(1);
        SASSERT(k > 1);
       
        auto x0 = div(a, num_t(k));
        auto x1 = div((x0 * num_t(k - 1)) + div(a, power_of(x0, k - 1)), num_t(k));

        while (x1 < x0)	{
            x0 = x1;
            x1 = div((x0 * num_t(k - 1)) + div(a, power_of(x0, k - 1)), num_t(k));
        }
        return x0;
    }

    template<typename num_t>
    vector<num_t> const& arith_base<num_t>::factor(num_t n) {
        m_factors.reset();
        if (n == 0)
            return m_factors;
        for (auto d : { 2, 3, 5 }) {
            while (mod(n, num_t(d)) == 0) {
                m_factors.push_back(num_t(d));
                n = div(n, num_t(d));
            }
        }
        static int increments[8] = { 4, 2, 4, 2, 4, 6, 2, 6 };
        unsigned i = 0, j = 0;
        for (auto d = num_t(7); d * d <= n && j < 3; d += num_t(increments[i++]), ++j) {
            while (mod(n, d) == 0) {
                m_factors.push_back(d);
                n = div(n, d);
            }
            if (i == 8)
                i = 0;       
        }
        if (n > 1)
            m_factors.push_back(n);
        return m_factors;
    }

    // switch to dscore mode
    template<typename num_t>
    void arith_base<num_t>::on_rescale() {
        m_dscore_mode = true;
    }

    template<typename num_t>
    void arith_base<num_t>::on_restart() {
#if 0
        for (var_t v = 0; v < m_vars.size(); ++v) {
            auto& vi = m_vars[v];
            num_t new_value;
            if (vi.m_def_idx == UINT_MAX) {
                auto val = value(v);
                
                if (ctx.rand(10) != 0) {
                    new_value = num_t((int)ctx.rand(2));
                    if (!in_bounds(v, new_value))
                        new_value = val;
                }
                else
                    new_value = val;
                vi.m_value = new_value;
            }
            else {
                vi.m_value = value1(v);
            }
            ctx.new_value_eh(vi.m_expr);           
        }

        for (sat::bool_var v = 0; v < ctx.num_bool_vars(); ++v) {
            auto* ineq = atom(v);
            if (!ineq)
                continue;
            ineq->m_args_value = ineq->m_coeff;
            for (auto const& [coeff, w] : ineq->m_args) 
                ineq->m_args_value += coeff * value(w);
            init_bool_var(v);
        }
#endif
    }

    template<typename num_t>
    void arith_base<num_t>::check_ineqs() {
        for (unsigned bv = 0; bv < ctx.num_bool_vars(); ++bv) {
            auto const* ineq = get_ineq(bv);
            if (!ineq)
                continue;
            num_t d = dtt(sign(bv), *ineq);
            sat::literal lit(bv, sign(bv));
            if (ctx.is_true(lit) != (d == 0)) {
                verbose_stream() << "invalid assignment " << bv << " " << *ineq << "\n";
            }
            VERIFY(ctx.is_true(lit) == (d == 0));
        }
    }

    template<typename num_t>
    void arith_base<num_t>::register_term(expr* _e) {
        if (!is_app(_e))
            return;
        app* e = to_app(_e);
        auto v = ctx.atom2bool_var(e);
        if (v != sat::null_bool_var)
            init_bool_var(v);
        if (!a.is_arith_expr(e) && !m.is_eq(e) && !m.is_distinct(e))
            for (auto arg : *e)
                if (a.is_int_real(arg))
                    mk_term(arg);
    }

    template<typename num_t>
    bool arith_base<num_t>::is_distinct(expr* e) {
        return m.is_distinct(e) &&
            to_app(e)->get_num_args() > 0 &&
            a.is_int_real(to_app(e)->get_arg(0));
    }

    template<typename num_t>
    bool arith_base<num_t>::eval_distinct(expr* e) {
        auto const& args = *to_app(e);
        for (unsigned i = 0; i < args.get_num_args(); ++i)
            for (unsigned j = i + 1; j < args.get_num_args(); ++j) {
                auto v1 = mk_term(args.get_arg(i));
                auto v2 = mk_term(args.get_arg(j));
                if (value(v1) == value(v2))
                    return false;
            }
        return true;
    }

    template<typename num_t>
    void arith_base<num_t>::repair_distinct(expr* e) {
        auto const& args = *to_app(e);
        for (unsigned i = 0; i < args.get_num_args(); ++i)
            for (unsigned j = i + 1; j < args.get_num_args(); ++j) {
                auto v1 = mk_term(args.get_arg(i));
                auto v2 = mk_term(args.get_arg(j));
                verbose_stream() << "repair " << v1 << " " << v2 << " " 
                    << value(v1) << " " << value(v2) << "\n";
                if (value(v1) == value(v2)) {
                    auto new_value = value(v1) + num_t(1);
                    if (new_value == value(v2))
                        new_value += num_t(1);
                    if (!is_fixed(v2))
                        update(v2, new_value);
                    else if (!is_fixed(v1))
                        update(v1, new_value);
                }
            }
    }

    template<typename num_t>
    bool arith_base<num_t>::set_value(expr* e, expr* v) {

        if (!a.is_int_real(e))
            return false;
        var_t w = m_expr2var.get(e->get_id(), UINT_MAX);
        if (w == UINT_MAX)
            w = mk_term(e);

        num_t n;
        try {
            if (!is_num(v, n))
                return false;
        }
        catch (overflow_exception const&) {
            return false;
        }
        if (n == value(w))
            return true;
         bool r = update(w, n);   

         if (!r) {
             IF_VERBOSE(2,
                 verbose_stream() << "set value failed " << mk_pp(e, m) << " := " << mk_pp(v, m) << "\n";
                display(verbose_stream(), w) << " := " << value(w) << "\n");
         }
         return r;
    }

    template<typename num_t>
    expr_ref arith_base<num_t>::get_value(expr* e) {
        num_t n;
        if (is_num(e, n))
            return expr_ref(a.mk_numeral(n.to_rational(), a.is_int(e)), m);
        auto v = mk_term(e);
        return expr_ref(a.mk_numeral(m_vars[v].value().to_rational(), a.is_int(e)), m);
    }

    template<typename num_t>
    bool arith_base<num_t>::is_fixed(expr* e, expr_ref& value) {
        if (!a.is_int_real(e))
            return false;
        num_t n;
        if (is_num(e, n)) {
            value = expr_ref(a.mk_numeral(n.to_rational(), a.is_int(e)), m);
            return true;
        }
        auto v = mk_term(e);
        if (is_fixed(v)) {
            value = expr_ref(a.mk_numeral(m_vars[v].value().to_rational(), a.is_int(e)), m);
            return true;
        }
        return false;
    }

    template<typename num_t>
    bool arith_base<num_t>::is_sat() {
        invariant();
        for (auto const& clause : ctx.clauses()) {
            bool sat = false;
            for (auto lit : clause.m_clause) {
                if (!ctx.is_true(lit))
                    continue;
                if (is_distinct(ctx.atom(lit.var()))) {
                    if (eval_distinct(ctx.atom(lit.var())) != lit.sign()) {
                        sat = true;
                        break;
                    }
                    continue;
                }
                auto ineq = get_ineq(lit.var());
                if (!ineq) {
                    sat = true;
                    break;
                }
                if (ineq->is_true() != lit.sign()) {
                    sat = true;
                    break;
                }
            }
            if (sat)
                continue;
            verbose_stream() << "not sat:\n";
            verbose_stream() << clause << "\n";
            for (auto lit : clause.m_clause) {
                verbose_stream() << lit << " (" << ctx.is_true(lit) << ") ";
                auto ineq = get_ineq(lit.var());
                if (!ineq)
                    continue;
                verbose_stream() << *ineq << "\n";
                for (auto const& [coeff, v] : ineq->m_args)
                    verbose_stream() << coeff << " " << v << " " << mk_bounded_pp(m_vars[v].m_expr, m) << " := " << value(v) << "\n";
            }
            exit(0);
            if (!sat)
                return false;
        }
        return true;
    }

    template<typename num_t>
    std::ostream& arith_base<num_t>::display(std::ostream& out, mul_def const& md) const {
        auto const& [w, monomial] = md;
        bool first = true;
        for (auto [v, p] : monomial) {
            if (!first)
                out << " * ";
            out << "v" << v;
            if (p > 1)
                out << "^" << p;
            first = false;
        }
        return out;
    }

    template<typename num_t>
    std::ostream& arith_base<num_t>::display(std::ostream& out, add_def const& ad) const {
        bool first = true;
        for (auto [c, w] : ad.m_args) {
            if (first && c == 1)
                ;
            else if (first && c == -1)
                out << "-";
            else if (first)
                out << c << "*";
            else if (c == 1)
                out << " + ";
            else if (c == - 1)
                out << " - ";
            else if (c > 0)
                out << " + " << c << "*";
            else
                out << " - " << -c << "*";
            first = false;
            out << "v" << w;
        }
        if (ad.m_args.empty())
            out << ad.m_coeff;
        else if (ad.m_coeff > 0)
            out << " + " << ad.m_coeff;
        else if (ad.m_coeff < 0)
            out << " - " << -ad.m_coeff;
        return out;
    }

    template<typename num_t>
    std::ostream& arith_base<num_t>::display(std::ostream& out, var_t v) const {
        auto const& vi = m_vars[v];
        auto const& lo = vi.m_lo;
        auto const& hi = vi.m_hi;
        out << "v" << v << " := " << vi.value() << " ";
        if (lo || hi) {
            if (lo)
                out << (lo->is_strict ? "(": "[") << lo->value;
            else
                out << "(";
            out << " ";
            if (hi)
                out << hi->value << (hi->is_strict ? ")" : "]");
            else
                out << ")";
            out << " ";
        }
        out << mk_bounded_pp(vi.m_expr, m) << " ";
        if (is_add(v)) 
            display(out << "add: ", get_add(v)) << " ";
        if (is_mul(v))
            display(out << "mul: ", get_mul(v)) << " ";

        if (!vi.m_adds.empty()) {
            out << " adds: ";
            for (auto v : vi.m_adds)
                out << "v" << m_adds[v].m_var << " ";
            out << " ";
        }

        if (!vi.m_muls.empty()) {
            out << " muls: ";
            for (auto v : vi.m_muls)
                out << "v" << m_muls[v].m_var << " ";
            out << " ";
        }
        
        if (!vi.m_ineqs.empty()) {
            out << " bool: ";
            for (auto [c, bv] : vi.m_ineqs)
                out << c << "@" << bv << " ";
        }
        return out;
    }

    template<typename num_t>
    std::ostream& arith_base<num_t>::display(std::ostream& out) const {
        for (unsigned v = 0; v < ctx.num_bool_vars(); ++v) {
            auto ineq = get_ineq(v);
            if (ineq)
                out << v << ": " << *ineq << "\n";
        }
        for (unsigned v = 0; v < m_vars.size(); ++v)
            display(out, v) << "\n";
        
        for (auto md : m_muls) {
            out << "v" << md.m_var << " := ";
            for (auto [w, p] : md.m_monomial) {
                out << "v" << w;
                if (p > 1)
                    out << "^" << p;
                out << " ";
            }

            out << "\n";
        }

        for (auto od : m_ops) {
            out << "v" << od.m_var << " := ";
            out << "v" << od.m_arg1 << " op-" << od.m_op << " v" << od.m_arg2 << "\n";
        }
        return out;
    }

    template<typename num_t>
    bool arith_base<num_t>::eval_is_correct(var_t v) {
        auto const& vi = m_vars[v];
        if (vi.m_def_idx == UINT_MAX)
            return true;
        IF_VERBOSE(4, verbose_stream() << vi.m_op << " repair def " << mk_bounded_pp(vi.m_expr, m) << "\n");
        TRACE("sls", tout << "repair def " << mk_bounded_pp(vi.m_expr, m) << "\n");
        switch (vi.m_op) {
        case arith_op_kind::LAST_ARITH_OP:
            break;
        case arith_op_kind::OP_ADD: {
            auto ad = m_adds[vi.m_def_idx];
            num_t sum(ad.m_coeff);
            for (auto [c, w] : ad.m_args)
                sum += c * value(w);
            return sum == value(v);
        }
        case arith_op_kind::OP_MUL: {
            auto md = m_muls[vi.m_def_idx];
            num_t prod(1);
            for (auto [w, p] : md.m_monomial)
                prod *= power_of(value(w), p);
            return prod == value(v);
        }
        case arith_op_kind::OP_MOD: {
            auto od = m_ops[vi.m_def_idx];
            return value(v) == (value(od.m_arg2) == 0 ? num_t(0) : mod(value(od.m_arg1), value(od.m_arg2)));
        }
        case arith_op_kind::OP_REM: {
            auto od = m_ops[vi.m_def_idx];
            return value(v) == (value(od.m_arg2) == 0 ? num_t(0) : mod(value(od.m_arg1), value(od.m_arg2)));
        }
        case arith_op_kind::OP_POWER: {
            auto od = m_ops[vi.m_def_idx];
            NOT_IMPLEMENTED_YET();
            break;
        }
        case arith_op_kind::OP_IDIV: {
            auto od = m_ops[vi.m_def_idx];
            return value(v) == (value(od.m_arg2) == 0 ? num_t(0) : div(value(od.m_arg1), value(od.m_arg2)));
        }           
        case arith_op_kind::OP_DIV: {
            auto od = m_ops[vi.m_def_idx];
            return value(v) == (value(od.m_arg2) == 0 ? num_t(0) : value(od.m_arg1) / value(od.m_arg2));
        }
        case arith_op_kind::OP_ABS: {
            auto od = m_ops[vi.m_def_idx];
            return value(v) == abs(value(od.m_arg1));
        }
        case arith_op_kind::OP_TO_INT: {
            // auto od = m_ops[vi.m_def_idx];
            NOT_IMPLEMENTED_YET();
            break;
        }
        case arith_op_kind::OP_TO_REAL: {
            // auto od = m_ops[vi.m_def_idx];
            NOT_IMPLEMENTED_YET();
            break;
        }
        default: {
            NOT_IMPLEMENTED_YET();
            break;
        }
        }
        return true;
    }

    template<typename num_t>
    void arith_base<num_t>::invariant() {
        for (unsigned v = 0; v < ctx.num_bool_vars(); ++v) {
            auto ineq = get_ineq(v);
            if (ineq)
                invariant(*ineq);
        }
        auto& out = verbose_stream();
        for (var_t v = 0; v < m_vars.size(); ++v) {
            if (!eval_is_correct(v)) {

                display(out);
                display(out, v) << "\n";
                out << mk_bounded_pp(m_vars[v].m_expr, m) << "\n";

                if (is_mul(v)) {
                    auto const& [w, monomial] = get_mul(v);
                    num_t prod(1);
                    for (auto [v, p] : monomial)
                        prod *= power_of(value(v), p);
                    out << "product " << prod << " value " << value(w) << "\n";
                    out << "v" << w << " := ";
                    for (auto [w, p] : monomial) {
                        out << "(v" << w;
                        if (p > 1)
                            out << "^" << p;
                        out << " := " << value(w);
                        out << ") ";
                    }
                    out << "\n";
                }
                else if (is_add(v)) {
                    auto const& ad = get_add(v);
                    out << "v" << ad.m_var << " := ";
                    display(out, ad) << "\n";
                }

                UNREACHABLE();
            }
        }
    }

    template<typename num_t>
    void arith_base<num_t>::invariant(ineq const& i) {
        num_t val = i.m_coeff;
        for (auto const& [c, v] : i.m_args)
            val += c * value(v);
        if (val != i.m_args_value)
            verbose_stream() << val << ": " << i << "\n";
        SASSERT(val == i.m_args_value);
        VERIFY(val == i.m_args_value);
    }


    template<typename num_t>
    void arith_base<num_t>::collect_statistics(statistics& st) const {
        st.update("sls-arith-flips", m_stats.m_num_steps);
    }

    template<typename num_t>
    void arith_base<num_t>::reset_statistics() {
        m_stats.m_num_steps = 0;
    }
}

template class sls::arith_base<checked_int64<true>>;
template class sls::arith_base<rational>;
