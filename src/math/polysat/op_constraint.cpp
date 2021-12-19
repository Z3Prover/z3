/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat constraints for bit operations.

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2021-12-09

Notes:

Additional possible functionality on constraints:

- activate - when operation is first activated. It may be created and only activated later.
- bit-wise assignments - narrow based on bit assignment, not entire word assignment.
- integration with congruence tables
- integration with conflict resolution

--*/

#include "math/polysat/op_constraint.h"
#include "math/polysat/solver.h"

namespace polysat {

    op_constraint::op_constraint(constraint_manager& m, code c, pdd const& p, pdd const& q, pdd const& r) :
        constraint(m, ckind_t::op_t), m_op(c), m_p(p), m_q(q), m_r(r) {
        m_vars.append(p.free_vars());
        for (auto v : q.free_vars())
            if (!m_vars.contains(v))
                m_vars.push_back(v);
        for (auto v : r.free_vars())
            if (!m_vars.contains(v))
                m_vars.push_back(v);

        switch (c) {
        case code::and_op:
        case code::or_op:
        case code::xor_op:
            if (p.index() > q.index())
                std::swap(m_p, m_q);
            break;
        default:
            break;
        }
    }

    lbool op_constraint::eval(pdd const& p, pdd const& q, pdd const& r) const {
        switch (m_op) {
        case code::lshr_op:
            return eval_lshr(p, q, r);
        default:
            return l_undef;
        }
    }

    bool op_constraint::is_always_false(bool is_positive, pdd const& p, pdd const& q, pdd const& r) const {
        switch (eval(p, q, r)) {
        case l_true: return !is_positive;
        case l_false: return is_positive;
        default: return false;
        }
    }

    bool op_constraint::is_always_true(bool is_positive, pdd const& p, pdd const& q, pdd const& r) const {
        switch (eval(p, q, r)) {
        case l_true: return is_positive;
        case l_false: return !is_positive;
        default: return false;
        }
    }

    bool op_constraint::is_always_false(bool is_positive) const {
        return is_always_false(is_positive, p(), q(), r());
    }

    bool op_constraint::is_currently_false(assignment_t const& a, bool is_positive) const {
        return is_always_false(is_positive, p().subst_val(a), q().subst_val(a), r().subst_val(a));
    }

    bool op_constraint::is_currently_true(assignment_t const& a, bool is_positive) const {
        return is_always_true(is_positive, p().subst_val(a), q().subst_val(a), r().subst_val(a));
    }

    std::ostream& op_constraint::display(std::ostream& out, lbool status) const {
        switch (status) {
        case l_true: return display(out);
        case l_false: return display(out << "~");
        default: return display(out << "?");
        }
    }

    std::ostream& operator<<(std::ostream& out, op_constraint::code c) {
        switch (c) {
        case op_constraint::code::ashr_op:
            return out << ">>a";
        case op_constraint::code::lshr_op:
            return out << ">>";
        case op_constraint::code::shl_op:
            return out << "<<";
        case op_constraint::code::and_op:
            return out << "&";
        case op_constraint::code::or_op:
            return out << "|";
        case op_constraint::code::xor_op:
            return out << "^";
        default:
            UNREACHABLE();
            return out;
        }
        return out;
    }

    std::ostream& op_constraint::display(std::ostream& out) const {
        if (m_op == code::not_op)
            return out << r() << " == ~" << p();
        else
            return out << r() << " == " << p() << " " << m_op << " " << q();
    }

    /**
    * Propagate consequences or detect conflicts based on partial assignments.
    *
    * We can assume that op_constraint is only asserted positive.
    */

    void op_constraint::narrow(solver& s, bool is_positive) {
        SASSERT(is_positive);

        if (is_currently_true(s.assignment(), is_positive))
            return;

        switch (m_op) {
        case code::lshr_op:
            narrow_lshr(s);
            break;
        case code::and_op:
            narrow_and(s);
            break;
        default:
            NOT_IMPLEMENTED_YET();
            break;
        }
        if (!s.is_conflict() && is_currently_false(s.assignment(), is_positive))
            s.set_conflict(signed_constraint(this, is_positive));
    }

    unsigned op_constraint::hash() const {
        return mk_mix(p().hash(), q().hash(), r().hash());
    }

    bool op_constraint::operator==(constraint const& other) const {
        if (other.kind() != ckind_t::op_t)
            return false;
        auto const& o = other.to_op();
        return m_op == o.m_op && p() == o.p() && q() == o.q() && r() == o.r();
    }

    /**
     * Enforce basic axioms for r == p >> q:
     *
     * q >= k -> r[i] = 0 for i > K - k
     * q >= K -> r = 0
     * q >= k -> r <= 2^{K-k-1}
     * q = k -> r[i - k] = p[i] for i <= K - k
     * r <= p
     * q != 0 => r <= p
     * q = 0 => r = p
     *
     * when q is a constant, several axioms can be enforced at activation time.
     *
     * Enforce also inferences and bounds
     *
     * TODO use also
     * s.m_viable.min_viable();
     * s.m_viable.max_viable()
     * when r, q are variables.
     */
    void op_constraint::narrow_lshr(solver& s) {
        auto pv = p().subst_val(s.assignment());
        auto qv = q().subst_val(s.assignment());
        auto rv = r().subst_val(s.assignment());
        unsigned K = p().manager().power_of_2();

        signed_constraint lshr(this, true);

        if (pv.is_val() && rv.is_val() && rv.val() > pv.val())
            // r <= p
            s.add_clause(~lshr, s.ule(r(), p()), true);
        else if (qv.is_val() && qv.val() >= K && rv.is_val() && !rv.is_zero())
            // q >= K -> r = 0
            s.add_clause(~lshr, ~s.ule(K, q()), s.eq(r()), true);
        else if (qv.is_zero() && pv.is_val() && rv.is_val() && pv != rv)
            // q = 0 -> p = r
            s.add_clause(~lshr, ~s.eq(q()), s.eq(p(), r()), true);
        else if (qv.is_val() && !qv.is_zero() && pv.is_val() && rv.is_val() && !pv.is_zero() && pv.val() <= rv.val())
            // q != 0 & p > 0 => r < p 
            s.add_clause(~lshr, s.eq(q()), s.ule(p(), 0), s.ult(r(), p()), true);
        else if (qv.is_val() && !qv.is_zero() && qv.val() < K && rv.is_val() &&
            rv.val() > rational::power_of_two(K - qv.val().get_unsigned() - 1))
            // q >= k -> r <= 2^{K-k-1}
            s.add_clause(~lshr, ~s.ule(qv.val(), q()), s.ule(r(), rational::power_of_two(K - qv.val().get_unsigned() - 1)), true);
        else if (qv.is_val() && qv.val() >= K && rv.is_val() && !rv.is_zero())
            // q >= K -> r = 0
            s.add_clause(~lshr, ~s.ule(K, q()), s.eq(r()), true);            
        // q = k -> r[i - k] = p[i] for K - k <= i < K
        else if (pv.is_val() && rv.is_val() && qv.is_val() && !qv.is_zero()) {
            unsigned k = qv.val().get_unsigned();
            for (unsigned i = K - k; i < K; ++i) {
                if (rv.val().get_bit(i - k) && !pv.val().get_bit(i)) {
                    s.add_clause(~lshr, ~s.eq(q(), k), ~s.bit(r(), i - k), s.bit(p(), i), true);
                    return;
                }
                if (!rv.val().get_bit(i - k) && pv.val().get_bit(i)) {
                    s.add_clause(~lshr, ~s.eq(q(), k), s.bit(r(), i - k), ~s.bit(p(), i), true);
                    return;
                }
            }
        }
        else {
            SASSERT(!(pv.is_val() && qv.is_val() && rv.is_val()));
        }
    }

    lbool op_constraint::eval_lshr(pdd const& p, pdd const& q, pdd const& r) const {
        auto& m = p.manager();

        if (p.is_val() && q.is_val() && r.is_val())
            return r == p * m.mk_val(rational::power_of_two(q.val().get_unsigned())) ? l_true : l_false;
            
        if (q.is_val() && q.val() >= m.power_of_2() && r.is_val())
            return r.is_zero() ? l_true : l_false;
                
        // other cases when we know lower 
        // bound of q, e.g, q = 2^k*q1 + q2, where q2 is a constant.
        return l_undef;
    }

    /**
    * Produce lemmas:
    * p & q <= p
    * p & q <= q
    * p = q => p & q = r
    * p = 0 => r = 0
    * q = 0 => r = 0
    * p[i] && q[i] = r[i]
    * 
    * Possible other:
    * p = max_value => q = r
    * q = max_value => p = r
    */
    void op_constraint::narrow_and(solver& s) {
        auto pv = p().subst_val(s.assignment());
        auto qv = q().subst_val(s.assignment());
        auto rv = r().subst_val(s.assignment());

        signed_constraint andc(this, true);
        if (pv.is_val() && rv.is_val() && rv.val() > pv.val())
            s.add_clause(~andc, s.ule(r(), p()), true);
        else if (qv.is_val() && rv.is_val() && rv.val() > qv.val())
            s.add_clause(~andc, s.ule(r(), q()), true);
        else if (pv.is_val() && qv.is_val() && rv.is_val() && pv == qv && rv != pv)
            s.add_clause(~andc, ~s.eq(p(), q()), s.eq(r(), p()), true);
        else if (pv.is_zero() && rv.is_val() && !rv.is_zero())
            s.add_clause(~andc, ~s.eq(p()), s.eq(r()), true);
        else if (qv.is_zero() && rv.is_val() && !rv.is_zero())
            s.add_clause(~andc, ~s.eq(q()), s.eq(r()), true);
        else if (pv.is_val() && qv.is_val() && rv.is_val()) {
            unsigned K = p().manager().power_of_2();
            for (unsigned i = 0; i < K; ++i) {
                bool pb = pv.val().get_bit(i);
                bool qb = qv.val().get_bit(i);
                bool rb = rv.val().get_bit(i);
                if (rb == (pb && qb))
                    continue;
                if (pb && qb && !rb)
                    s.add_clause(~andc, ~s.bit(p(), i), ~s.bit(q(), i), s.bit(r(), i), true);
                else if (!pb && rb)
                    s.add_clause(~andc, s.bit(p(), i), ~s.bit(r(), i), true);
                else if (!qb && rb)
                    s.add_clause(~andc, s.bit(q(), i), ~s.bit(r(), i), true);
                else
                    UNREACHABLE();
                return;
            }
        }
    }
}
