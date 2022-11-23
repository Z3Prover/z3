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
        // The following can currently not be used as standalone constraints
        SASSERT(c != code::or_op);
        SASSERT(c != code::xor_op);
        SASSERT(c != code::not_op);
    }

    lbool op_constraint::eval() const {
        return eval(p(), q(), r());
    }

    lbool op_constraint::eval(assignment const& a) const {
        return eval(a.apply_to(p()), a.apply_to(q()), a.apply_to(r()));
    }

    lbool op_constraint::eval(pdd const& p, pdd const& q, pdd const& r) const {
        switch (m_op) {
        case code::lshr_op:
            return eval_lshr(p, q, r);
        case code::shl_op:
            return eval_shl(p, q, r);
        case code::and_op:
            return eval_and(p, q, r);
        default:
            return l_undef;
        }
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
    void op_constraint::narrow(solver& s, bool is_positive, bool first) {
        SASSERT(is_positive);

        if (is_currently_true(s, is_positive))
            return;

        switch (m_op) {
        case code::lshr_op:
            narrow_lshr(s);
            break;
        case code::shl_op:
            narrow_shl(s);
            break;
        case code::and_op:
            narrow_and(s);
            break;
        default:
            NOT_IMPLEMENTED_YET();
            break;
        }
        if (!s.is_conflict() && is_currently_false(s, is_positive))
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
     *      q >= K  ->  r = 0
     *      q >= k  ->  r[i] = 0 for K - k <= i < K     (bit indices range from 0 to K-1, inclusive)
     *      q >= k  ->  r <= 2^{K-k} - 1
     *      q = k   ->  r[i] = p[i+k] for 0 <= i < K - k
     *      r <= p
     *      q != 0  ->  r <= p      (subsumed by previous axiom)
     *      q != 0  /\  p > 0 ->  r < p
     *      q = 0   ->  r = p
     *
     * when q is a constant, several axioms can be enforced at activation time.
     *
     * Enforce also inferences and bounds
     *
     * TODO: use also
     * s.m_viable.min_viable();
     * s.m_viable.max_viable()
     * when r, q are variables.
     */
    void op_constraint::narrow_lshr(solver& s) {
        auto const pv = s.subst(p());
        auto const qv = s.subst(q());
        auto const rv = s.subst(r());
        unsigned const K = p().manager().power_of_2();

        signed_constraint const lshr(this, true);

        if (pv.is_val() && rv.is_val() && rv.val() > pv.val())
            // r <= p
            s.add_clause(~lshr, s.ule(r(), p()), true);
        else if (qv.is_val() && qv.val() >= K && rv.is_val() && !rv.is_zero())
            // q >= K -> r = 0
            s.add_clause(~lshr, ~s.ule(K, q()), s.eq(r()), true);
        else if (qv.is_zero() && pv.is_val() && rv.is_val() && pv != rv)
            // q = 0 -> p = r
            s.add_clause(~lshr, ~s.eq(q()), s.eq(p(), r()), true);
        else if (qv.is_val() && !qv.is_zero() && pv.is_val() && rv.is_val() && !pv.is_zero() && rv.val() >= pv.val())
            // q != 0 & p > 0 -> r < p
            s.add_clause(~lshr, s.eq(q()), s.ule(p(), 0), s.ult(r(), p()), true);
        else if (qv.is_val() && !qv.is_zero() && qv.val() < K && rv.is_val() &&
            rv.val() > rational::power_of_two(K - qv.val().get_unsigned()) - 1)
            // q >= k -> r <= 2^{K-k} - 1
            s.add_clause(~lshr, ~s.ule(qv.val(), q()), s.ule(r(), rational::power_of_two(K - qv.val().get_unsigned()) - 1), true);
        else if (pv.is_val() && rv.is_val() && qv.is_val() && !qv.is_zero()) {
            unsigned const k = qv.val().get_unsigned();
            // q = k  ->  r[i] = p[i+k] for 0 <= i < K - k
            for (unsigned i = 0; i < K - k; ++i) {
                if (rv.val().get_bit(i) && !pv.val().get_bit(i + k)) {
                    s.add_clause(~lshr, ~s.eq(q(), k), ~s.bit(r(), i), s.bit(p(), i + k), true);
                    return;
                }
                if (!rv.val().get_bit(i) && pv.val().get_bit(i + k)) {
                    s.add_clause(~lshr, ~s.eq(q(), k), s.bit(r(), i), ~s.bit(p(), i + k), true);
                    return;
                }
            }
        }
        else {
            SASSERT(!(pv.is_val() && qv.is_val() && rv.is_val()));
        }
    }

    /** Evaluate constraint: r == p >> q */
    lbool op_constraint::eval_lshr(pdd const& p, pdd const& q, pdd const& r) {
        auto& m = p.manager();

        if (q.is_zero() && p == r)
            return l_true;

        if (q.is_val() && q.val() >= m.power_of_2() && r.is_val())
            return to_lbool(r.is_zero());

        if (p.is_val() && q.is_val() && r.is_val()) {
            SASSERT(q.val().is_unsigned());  // otherwise, previous condition should have been triggered
            // TODO: use right-shift operation instead of division
            auto divisor = rational::power_of_two(q.val().get_unsigned());
            return to_lbool(r.val() == div(p.val(), divisor));
        }

        // TODO: other cases when we know lower bound of q,
        //       e.g, q = 2^k*q1 + q2, where q2 is a constant.
        return l_undef;
    }

    /**
     * Enforce axioms for constraint: r == p << q
     *
     *      q >= K  ->  r = 0
     *      q >= k  ->  r = 0  \/  r >= 2^k
     *      q >= k  ->  r[i] = 0 for i < k
     *      q = k   ->  r[i+k] = p[i] for 0 <= i < K - k
     *      r != 0  ->  r >= p
     *      q = 0   ->  r = p
     */
    void op_constraint::narrow_shl(solver& s) {
        auto const pv = s.subst(p());
        auto const qv = s.subst(q());
        auto const rv = s.subst(r());
        unsigned const K = p().manager().power_of_2();

        signed_constraint const shl(this, true);

        if (pv.is_val() && !pv.is_zero() && !pv.is_one() && rv.is_val() && !rv.is_zero() && rv.val() < pv.val())
            // r != 0  ->  r >= p
            // r = 0 \/ r >= p      (equivalent)
            // r-1 >= p-1           (equivalent unit constraint to better support narrowing)
            s.add_clause(~shl, s.ule(p() - 1, r() - 1), true);
        else if (qv.is_val() && qv.val() >= K && rv.is_val() && !rv.is_zero())
            // q >= K  ->  r = 0
            s.add_clause(~shl, ~s.ule(K, q()), s.eq(r()), true);
        else if (qv.is_zero() && pv.is_val() && rv.is_val() && rv != pv)
            // q = 0  ->  r = p
            s.add_clause(~shl, ~s.eq(q()), s.eq(r(), p()), true);
        else if (qv.is_val() && !qv.is_zero() && qv.val() < K && rv.is_val() &&
            !rv.is_zero() && rv.val() < rational::power_of_two(qv.val().get_unsigned()))
            // q >= k  ->  r = 0  \/  r >= 2^k  (intuitive version)
            // q >= k  ->  r - 1 >= 2^k - 1     (equivalent unit constraint to better support narrowing)
            s.add_clause(~shl, ~s.ule(qv.val(), q()), s.ule(rational::power_of_two(qv.val().get_unsigned()) - 1, r() - 1), true);
        else if (pv.is_val() && rv.is_val() && qv.is_val() && !qv.is_zero()) {
            unsigned const k = qv.val().get_unsigned();
            // q = k  ->  r[i+k] = p[i] for 0 <= i < K - k
            for (unsigned i = 0; i < K - k; ++i) {
                if (rv.val().get_bit(i + k) && !pv.val().get_bit(i)) {
                    s.add_clause(~shl, ~s.eq(q(), k), ~s.bit(r(), i + k), s.bit(p(), i), true);
                    return;
                }
                if (!rv.val().get_bit(i + k) && pv.val().get_bit(i)) {
                    s.add_clause(~shl, ~s.eq(q(), k), s.bit(r(), i + k), ~s.bit(p(), i), true);
                    return;
                }
            }
        }
        else {
            SASSERT(!(pv.is_val() && qv.is_val() && rv.is_val()));
        }
    }

    /** Evaluate constraint: r == p << q */
    lbool op_constraint::eval_shl(pdd const& p, pdd const& q, pdd const& r) {
        auto& m = p.manager();

        if (q.is_zero() && p == r)
            return l_true;

        if (q.is_val() && q.val() >= m.power_of_2() && r.is_val())
            return to_lbool(r.is_zero());

        if (p.is_val() && q.is_val() && r.is_val()) {
            SASSERT(q.val().is_unsigned());  // otherwise, previous condition should have been triggered
            // TODO: use left-shift operation instead of multiplication?
            auto factor = rational::power_of_two(q.val().get_unsigned());
            return to_lbool(r == p * m.mk_val(factor));
        }

        // TODO: other cases when we know lower bound of q,
        //       e.g, q = 2^k*q1 + q2, where q2 is a constant.
        //       (bounds should be tracked by viable, then just use min_viable here)
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
        auto pv = s.subst(p());
        auto qv = s.subst(q());
        auto rv = s.subst(r());

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

    /** Evaluate constraint: r == p & q */
    lbool op_constraint::eval_and(pdd const& p, pdd const& q, pdd const& r) {
        if ((p.is_zero() || q.is_zero()) && r.is_zero())
            return l_true;

        if (p.is_val() && q.is_val() && r.is_val())
            return r.val() == bitwise_and(p.val(), q.val()) ? l_true : l_false;

        return l_undef;
    }

    void op_constraint::add_to_univariate_solver(solver& s, univariate_solver& us, unsigned dep, bool is_positive) const {
        auto p_coeff = s.subst(p()).get_univariate_coefficients();
        auto q_coeff = s.subst(q()).get_univariate_coefficients();
        auto r_coeff = s.subst(r()).get_univariate_coefficients();
        switch (m_op) {
        case code::lshr_op:
            us.add_lshr(p_coeff, q_coeff, r_coeff, !is_positive, dep);
            break;
        case code::and_op:
            us.add_and(p_coeff, q_coeff, r_coeff, !is_positive, dep);
            break;
        default:
            NOT_IMPLEMENTED_YET();
            break;
        }
    }

}
