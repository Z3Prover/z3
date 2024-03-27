/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat constraints

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/

#include "util/log.h"
#include "sat/smt/polysat/core.h"
#include "sat/smt/polysat/constraints.h"
#include "sat/smt/polysat/ule_constraint.h"
#include "sat/smt/polysat/umul_ovfl_constraint.h"
#include "sat/smt/polysat/op_constraint.h"

namespace polysat {

    signed_constraint constraints::ule(pdd const& p, pdd const& q) {
        pdd lhs = p, rhs = q;
        bool is_positive = true;
        ule_constraint::simplify(is_positive, lhs, rhs);
        pdd unfold_lhs = c.ms().subst(lhs);
        pdd unfold_rhs = c.ms().subst(rhs);
        auto* cnstr = alloc(ule_constraint, lhs, rhs, unfold_lhs, unfold_rhs);
        c.trail().push(new_obj_trail(cnstr));
        auto sc = signed_constraint(ckind_t::ule_t, cnstr);
        return is_positive ? sc : ~sc;
    }

    signed_constraint constraints::umul_ovfl(pdd const& p, pdd const& q) {
        auto* cnstr = alloc(umul_ovfl_constraint, p, q);
        c.trail().push(new_obj_trail(cnstr));
        return signed_constraint(ckind_t::umul_ovfl_t, cnstr);
    }

    signed_constraint constraints::lshr(pdd const& a, pdd const& b, pdd const& r) {
        auto* cnstr = alloc(op_constraint, op_constraint::code::lshr_op, a, b, r);
        c.trail().push(new_obj_trail(cnstr));
        return signed_constraint(ckind_t::op_t, cnstr);
    }

    signed_constraint constraints::ashr(pdd const& a, pdd const& b, pdd const& r) {
        auto* cnstr = alloc(op_constraint, op_constraint::code::ashr_op, a, b, r);
        c.trail().push(new_obj_trail(cnstr));
        return signed_constraint(ckind_t::op_t, cnstr);
    }

    signed_constraint constraints::shl(pdd const& a, pdd const& b, pdd const& r) {
        auto* cnstr = alloc(op_constraint, op_constraint::code::shl_op, a, b, r);
        c.trail().push(new_obj_trail(cnstr));
        return signed_constraint(ckind_t::op_t, cnstr);
    }

    signed_constraint constraints::band(pdd const& a, pdd const& b, pdd const& r) {
        auto* cnstr = alloc(op_constraint, op_constraint::code::and_op, a, b, r);
        c.trail().push(new_obj_trail(cnstr));
        return signed_constraint(ckind_t::op_t, cnstr);
    }

    signed_constraint constraints::bor(pdd const& a, pdd const& b, pdd const& r) {
        auto* cnstr = alloc(op_constraint, op_constraint::code::or_op, a, b, r);
        c.trail().push(new_obj_trail(cnstr));
        return signed_constraint(ckind_t::op_t, cnstr);
    }

    // parity(p) >= k if low order k bits of p are 0.
    // Requires 0 <= k <= N.
    signed_constraint constraints::parity_at_least(pdd const& p, unsigned k) {
        auto& m = p.manager();
        unsigned N = m.power_of_2();
        // NOTE: it is ambiguous at this point what we want for k > N:
        //  - as a condition, parity(p) > N is never true
        //  - as an implied constraint, we usually want p == 0 instead
        VERIFY(k <= N);
        if (k == 0)
            // parity(p) >= 0 is a tautology
            return eq(m.zero());
        if (k == N)
            return eq(p);
        // parity(p) >= k
        // <=> p * 2^(N - k) == 0
        return eq(p * rational::power_of_two(N - k));
    }

    // parity(p) <= k.
    // Requires 0 <= k <= N.
    signed_constraint constraints::parity_at_most(pdd const& p, unsigned k) {
        auto& m = p.manager();
        unsigned N = m.power_of_2();
        if (k == N)
            // parity(p) <= N is a tautology
            return eq(m.zero());
        return ~parity_at_least(p, k + 1);
    }

    signed_constraint constraints::msb_ge(pdd const& p, unsigned k) {
        if (k == 0)
            return uge(p, 0);
        if (k > p.manager().power_of_2())
            return ult(p, 0);
        return uge(p, rational::power_of_two(k - 1));
    }

    signed_constraint constraints::msb_le(pdd const& p, unsigned k) {
        if (k == 0)
            return eq(p);
        if (k >= p.manager().power_of_2())
            return uge(p, 0);
        return ult(p, rational::power_of_two(k));
    }

    // 2^{N-i-1}* p >= 2^{N-1}
    signed_constraint constraints::bit(pdd const& p, unsigned i) {
        unsigned N = p.manager().power_of_2();
        return uge(p * rational::power_of_two(N - i - 1), rational::power_of_two(N - 1));
    }

    bool signed_constraint::is_eq(pvar& v, rational& val) {
        if (m_sign)
            return false;
        if (!is_ule())
            return false;
        auto const& ule = to_ule();
        auto const& l = ule.lhs(), &r = ule.rhs();
        if (!r.is_zero())
            return false;
        if (!l.is_unilinear())
            return false;
        if (!l.hi().is_one())
            return false;
        v = l.var();
        if (l.lo().val() == 0)
            val = 0;
        else 
            val = l.manager().two_to_N() - l.lo().val();
        return true;
    }

    lbool signed_constraint::weak_eval(assignment& a) const {
        lbool r = m_constraint->weak_eval(a);
        return m_sign ? ~r : r;
    }

    lbool signed_constraint::strong_eval(assignment& a) const {
        lbool r = m_constraint->strong_eval(a);
        return m_sign ? ~r : r;
    }

    std::ostream& signed_constraint::display(std::ostream& out) const {
        if (m_sign) out << "~";
        return out << *m_constraint;        
    }

}
