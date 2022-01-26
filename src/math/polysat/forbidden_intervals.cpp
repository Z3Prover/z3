/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Conflict explanation using forbidden intervals as described in
    "Solving bitvectors with MCSAT: explanations from bits and pieces"
    by S. Graham-Lengrand, D. Jovanovic, B. Dutertre.

Author:

    Jakob Rath 2021-04-6
    Nikolaj Bjorner (nbjorner) 2021-03-19

--*/
#include "math/polysat/forbidden_intervals.h"
#include "math/polysat/interval.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"

namespace polysat {

    /** 
     *
     * \param[in] c                 Original constraint
     * \param[in] v                 Variable that is bounded by constraint
     * \param[out] fi               "forbidden interval" record that captures values not allowed for v
     * \returns True iff a forbidden interval exists and the output parameters were set.
     */
    bool forbidden_intervals::get_interval(signed_constraint const& c, pvar v, fi_record& fi) {
        if (!c->is_ule())
            return false;
        
        struct backtrack {
            bool released = false;
            vector<signed_constraint>& side_cond;
            unsigned sz;
            backtrack(vector<signed_constraint>& s):side_cond(s), sz(s.size()) {}
            ~backtrack() {
                if (!released)
                    side_cond.shrink(sz);
            }
        };

        backtrack _backtrack(fi.side_cond);     

        fi.coeff = 1;
        fi.src = c;

        // eval(lhs) = a1*v + eval(e1) = a1*v + b1
        // eval(rhs) = a2*v + eval(e2) = a2*v + b2
        // We keep the e1, e2 around in case we need side conditions such as e1=b1, e2=b2.
        auto [ok1, a1, e1, b1] = linear_decompose(v, c->to_ule().lhs(), fi.side_cond);
        auto [ok2, a2, e2, b2] = linear_decompose(v, c->to_ule().rhs(), fi.side_cond);

        _backtrack.released = true;

        // v > q
        if (ok1 && !ok2 && match_non_zero(c, a1, b1, e1, fi))
            return true;

        // p > v
        if (!ok1 && ok2 && match_non_max(c, a2, b2, e2, fi))
            return true;

        if (!ok1 || !ok2 || (a1.is_zero() && a2.is_zero())) {
            _backtrack.released = false;
            return false;
        }
        SASSERT(b1.is_val());
        SASSERT(b2.is_val());

        // a*v <= 0, a odd
        if (match_zero(c, a1, b1, e1, a2, b2, e2, fi))
            return true;

        // a*v + b > 0, a odd
        if (match_non_zero_linear(c, a1, b1, e1, a2, b2, e2, fi))
            return true;

        if (match_linear1(c, a1, b1, e1, a2, b2, e2, fi))
            return true;
        if (match_linear2(c, a1, b1, e1, a2, b2, e2, fi))
            return true;
        if (match_linear3(c, a1, b1, e1, a2, b2, e2, fi))
            return true;
        if (match_linear4(c, a1, b1, e1, a2, b2, e2, fi))
            return true;

        _backtrack.released = false;
        return false;
    }

    void forbidden_intervals::push_eq(bool is_zero, pdd const& p, vector<signed_constraint>& side_cond) {
        SASSERT(!p.is_val() || (is_zero == p.is_zero()));
        if (p.is_val())
            return;
        else if (is_zero)
            side_cond.push_back(s.eq(p));
        else
            side_cond.push_back(~s.eq(p));
    }

    std::tuple<bool, rational, pdd, pdd> forbidden_intervals::linear_decompose(pvar v, pdd const& p, vector<signed_constraint>& out_side_cond) {
        auto& m = p.manager();
        pdd q = m.zero();
        pdd e = m.zero();
        unsigned const deg = p.degree(v);
        if (deg == 0)
            // p = 0*v + e
            e = p;
        else if (deg == 1)
            // p = q*v + e
            p.factor(v, 1, q, e);
        else
            return std::tuple(false, rational(0), q, e);

        // r := eval(q)
        // Add side constraint q = r.
        if (!q.is_val()) {
            pdd r = s.subst(q);
            if (!r.is_val())
                return std::tuple(false, rational(0), q, e);
            out_side_cond.push_back(s.eq(q, r));
            q = r;
        }
        auto b = s.subst(e); 
        return std::tuple(b.is_val(), q.val(), e, b);
    };

    eval_interval forbidden_intervals::to_interval(
        signed_constraint const& c, bool is_trivial, rational & coeff,
        rational & lo_val, pdd & lo,
        rational & hi_val, pdd & hi) {
        
        dd::pdd_manager& m = lo.manager();

        if (is_trivial) {
            if (c.is_positive())
                // TODO: we cannot use empty intervals for interpolation. So we
                // can remove the empty case (make it represent 'full' instead),
                // and return 'false' here. Then we do not need the proper/full
                // tag on intervals.
                return eval_interval::empty(m);
            else
                return eval_interval::full();
        }

        rational pow2 = m.max_value() + 1;

        if (coeff > pow2/2) {
            
            coeff = pow2 - coeff;
            SASSERT(coeff > 0);
            // Transform according to:  y \in [l;u[  <=>  -y \in [1-u;1-l[
            //      -y \in [1-u;1-l[
            //      <=>  -y - (1 - u) < (1 - l) - (1 - u)    { by: y \in [l;u[  <=>  y - l < u - l }
            //      <=>  u - y - 1 < u - l                   { simplified }
            //      <=>  (u-l) - (u-y-1) - 1 < u-l           { by: a < b  <=>  b - a - 1 < b }
            //      <=>  y - l < u - l                       { simplified }
            //      <=>  y \in [l;u[.
            lo = 1 - lo;
            hi = 1 - hi;
            swap(lo, hi);
            lo_val = mod(1 - lo_val, pow2);
            hi_val = mod(1 - hi_val, pow2);
            lo_val.swap(hi_val);
        }

        if (c.is_positive())
            return eval_interval::proper(lo, lo_val, hi, hi_val);
        else
            return eval_interval::proper(hi, hi_val, lo, lo_val);
    }

    /**
    * Match  e1 + t <= e2, with t = a1*y
    * condition for empty/full: e2 == -1
    */
    bool forbidden_intervals::match_linear1(signed_constraint const& c,
        rational const & a1, pdd const& b1, pdd const& e1, 
        rational const & a2, pdd const& b2, pdd const& e2,
        fi_record& fi) {
        if (a2.is_zero() && !a1.is_zero()) {
            SASSERT(!a1.is_zero());
            bool is_trivial = (b2 + 1).is_zero();
            push_eq(is_trivial, e2 + 1, fi.side_cond);
            auto lo = e2 - e1 + 1;
            rational lo_val = (b2 - b1 + 1).val();
            auto hi = -e1;
            rational hi_val = (-b1).val();
            fi.coeff = a1;
            fi.interval = to_interval(c, is_trivial, fi.coeff, lo_val, lo, hi_val, hi);
            add_non_unit_side_conds(fi, b1, e1, b2, e2);
            return true;
        }
        return false;
    }

    /**
     * e1 <= e2 + t, with t = a2*y
     * condition for empty/full: e1 == 0
     */
    bool forbidden_intervals::match_linear2(signed_constraint const& c,
        rational const & a1, pdd const& b1, pdd const& e1,
        rational const & a2, pdd const& b2, pdd const& e2,
        fi_record& fi) {
        if (a1.is_zero() && !a2.is_zero()) {
            SASSERT(!a2.is_zero());
            bool is_trivial = b1.is_zero();
            push_eq(is_trivial, e1, fi.side_cond);
            auto lo = -e2;
            rational lo_val = (-b2).val();
            auto hi = e1 - e2;
            rational hi_val = (b1 - b2).val();
            fi.coeff = a2;
            fi.interval = to_interval(c, is_trivial, fi.coeff, lo_val, lo, hi_val, hi);
            add_non_unit_side_conds(fi, b1, e1, b2, e2);
            return true;
        }
        return false;
    }

    /**
     * e1 + t <= e2 + t, with t = a1*y = a2*y
     * condition for empty/full: e1 == e2
     */
    bool forbidden_intervals::match_linear3(signed_constraint const& c,
        rational const & a1, pdd const& b1, pdd const& e1,
        rational const & a2, pdd const& b2, pdd const& e2,
        fi_record& fi) {
        if (a1 == a2 && !a1.is_zero()) {
            bool is_trivial = b1.val() == b2.val();
            push_eq(is_trivial, e1 - e2, fi.side_cond);
            auto lo = -e2;
            rational lo_val = (-b2).val();
            auto hi = -e1;
            rational hi_val = (-b1).val();
            fi.coeff = a1;
            fi.interval = to_interval(c, is_trivial, fi.coeff, lo_val, lo, hi_val, hi);
            add_non_unit_side_conds(fi, b1, e1, b2, e2);
            return true;
        }
        return false;
    }

    /**
     * e1 + t <= e2 + t', with t = a1*y, t' = a2*y, a1 != a2, a1, a2 non-zero
     */
    bool forbidden_intervals::match_linear4(signed_constraint const& c,
        rational const & a1, pdd const& b1, pdd const& e1,
        rational const & a2, pdd const& b2, pdd const& e2,
        fi_record& fi) {
        if (a1 != a2 && !a1.is_zero() && !a2.is_zero()) {
            // NOTE: we don't have an interval here in the same sense as in the other cases.
            // We use the interval to smuggle out the values a1,b1,a2,b2 without adding additional fields.
            // to_interval flips a1,b1 with a2,b2 for negative constraints, which we also need for this case.
            auto lo = b1;
            rational lo_val = a1;
            auto hi = b2;
            rational hi_val = a2;
            // We use fi.coeff = -1 to tell the caller to treat it as a diseq_lin.
            fi.coeff = -1;
            fi.interval = to_interval(c, false, fi.coeff, lo_val, lo, hi_val, hi);
            add_non_unit_side_conds(fi, b1, e1, b2, e2);
            SASSERT(!fi.interval.is_currently_empty());
            return true;
        }
        return false;
    }

    /**
     * a*v <= 0, a odd
     * forbidden interval for v is [1,0[
     *
     * TODO: extend to
     * 2^k*a*v <= 0, a odd
     * (using periodic intervals?)
     */
    bool forbidden_intervals::match_zero(
        signed_constraint const& c,
        rational const & a1, pdd const& b1, pdd const& e1,
        rational const & a2, pdd const& b2, pdd const& e2,
        fi_record& fi) {
        if (c.is_positive() && a1.is_odd() && b1.is_zero() && a2.is_zero() && b2.is_zero()) {
            auto& m = e1.manager();
            rational lo_val(1);
            auto lo = m.one();
            rational hi_val(0);
            auto hi = m.zero();
            fi.coeff = 1;
            fi.interval = eval_interval::proper(lo, lo_val, hi, hi_val);
            if (b1 != e1)
                fi.side_cond.push_back(s.eq(b1, e1));
            if (b2 != e2)
                fi.side_cond.push_back(s.eq(b2, e2));
            return true;
        }
        return false;
    }

    /**
     * a*v + b > 0, a odd
     *
     * TODO: extend to
     * 2^k*a*v + b > 0, a odd
     * (using periodic intervals?)
     */
    bool forbidden_intervals::match_non_zero_linear(
        signed_constraint const& c,
        rational const & a1, pdd const& b1, pdd const& e1,
        rational const & a2, pdd const& b2, pdd const& e2,
        fi_record& fi) {
        if (c.is_negative() && a1.is_odd() && a2.is_zero() && b2.is_zero()) {
            // a*v + b > 0
            // <=> a*v + b != 0
            // <=> v + a^-1 * b != 0
            // <=> v != - a^-1 * b
            auto& m = e1.manager();
            rational const& mod_value = m.two_to_N();
            rational a1_inv;
            VERIFY(a1.mult_inverse(m.power_of_2(), a1_inv));
            rational lo_val(mod(-b1.val() * a1_inv, mod_value));
            auto lo = -e1 * a1_inv;
            rational hi_val(mod(lo_val + 1, mod_value));
            auto hi = lo + 1;
            fi.coeff = 1;
            fi.interval = eval_interval::proper(lo, lo_val, hi, hi_val);
            if (b1 != e1)
                fi.side_cond.push_back(s.eq(b1, e1));
            if (b2 != e2)
                fi.side_cond.push_back(s.eq(b2, e2));
            return true;
        }
        return false;
    }

    /** 
     * v > q
     * forbidden interval for v is [0,1[
     * 
     * v - k > q
     * forbidden interval for v is [k,k+1[
     * 
     * a*v - k > q, a odd
     * forbidden interval for v is [a^-1*k, a^-1*k + 1[
     */
    bool forbidden_intervals::match_non_zero(
        signed_constraint const& c,
        rational const & a1, pdd const& b1, pdd const& e1,
        fi_record& fi) {
        if (a1.is_odd() && b1.is_zero() && !c.is_positive()) {
            auto& m = e1.manager();
            rational lo_val(0);
            auto lo = m.zero();
            rational hi_val(1);
            auto hi = m.one();
            fi.coeff = 1;
            fi.interval = eval_interval::proper(lo, lo_val, hi, hi_val);
            if (b1 != e1)
                fi.side_cond.push_back(s.eq(b1, e1));
            return true;
        }
        if (a1.is_odd() && b1.is_val() && !c.is_positive()) {
            auto& m = e1.manager();
            rational const& mod_value = m.two_to_N();
            rational a1_inv;
            VERIFY(a1.mult_inverse(m.power_of_2(), a1_inv));
            rational lo_val(mod(-b1.val() * a1_inv, mod_value));
            auto lo = -e1 * a1_inv;
            rational hi_val(mod(lo_val + 1, mod_value));
            auto hi = lo + 1;
            fi.coeff = 1;
            fi.interval = eval_interval::proper(lo, lo_val, hi, hi_val);
            if (b1 != e1)
                fi.side_cond.push_back(s.eq(b1, e1));
            return true;
        }
        return false;
    }

    /**
     * p > v
     * forbidden interval for v is [-1,0[
     * p > v + k
     * forbidden interval for v is [-k-1,-k[
     */
    bool forbidden_intervals::match_non_max(
        signed_constraint const& c,
        rational const & a2, pdd const& b2, pdd const& e2,
        fi_record& fi) {
        if (a2.is_one() && b2.is_val() && !c.is_positive()) {
            auto& m = e2.manager();
            rational const& mod_value = m.two_to_N();
            rational lo_val(mod(-b2.val() - 1, mod_value));
            auto lo = -e2 - 1;
            rational hi_val(mod(lo_val + 1, mod_value));
            auto hi = -e2;
            fi.coeff = 1;
            fi.interval = eval_interval::proper(lo, lo_val, hi, hi_val);
            if (b2 != e2)
                fi.side_cond.push_back(s.eq(b2, e2));
            return true;
        }
        return false;
    }


    void forbidden_intervals::add_non_unit_side_conds(fi_record& fi, pdd const& b1, pdd const& e1, pdd const& b2, pdd const& e2) {
        if (fi.coeff == 1)
            return;
        if (b1 != e1)
            fi.side_cond.push_back(s.eq(b1, e1));
        if (b2 != e2)
            fi.side_cond.push_back(s.eq(b2, e2));
    }
}
