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

    op_constraint::op_constraint(code c, pdd const& p, pdd const& q, pdd const& r) :
        constraint(ckind_t::op_t), m_op(c), m_p(p), m_q(q), m_r(r) {
        m_vars.append(p.free_vars());
        for (auto v : q.free_vars())
            if (!m_vars.contains(v))
                m_vars.push_back(v);
        for (auto v : r.free_vars())
            if (!m_vars.contains(v))
                m_vars.push_back(v);

        switch (c) {
        case code::and_op:
            if (p.index() > q.index())
                std::swap(m_p, m_q);
            break;
        case code::inv_op:
            SASSERT(q.is_zero());
        default:
            break;
        }
        VERIFY(r.is_var());
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
        case code::inv_op:
            return eval_inv(p, r);
        case code::udiv_op:
            return eval_udiv(p, q, r);
        case code::urem_op:
            return eval_urem(p, q, r);
        default:
            return l_undef;
        }
    }

    std::ostream& op_constraint::display(std::ostream& out, lbool status) const {
        switch (status) {
        case l_true: return display(out, "==");
        case l_false: return display(out, "!=");
        default: return display(out, "?=");
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
        case op_constraint::code::inv_op:
            return out << "inv";
        case op_constraint::code::udiv_op:
            return out << "/";
        case op_constraint::code::urem_op:
            return out << "%";
        default:
            UNREACHABLE();
            return out;
        }
        return out;
    }

    std::ostream& op_constraint::display(std::ostream& out) const {
        return display(out, l_true);
    }

    std::ostream& op_constraint::display(std::ostream& out, char const* eq) const {
        if (m_op == code::inv_op)
            return out << r() << " " << eq << " " << m_op << " " << p();

        return out << r() << " " << eq << " " << p() << " " << m_op << " " << q();
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

        if (first)
            activate(s);

        if (clause_ref lemma = produce_lemma(s, s.get_assignment()))
            s.add_clause(*lemma);

        if (!s.is_conflict() && is_currently_false(s, is_positive))
            s.set_conflict(signed_constraint(this, is_positive));
    }

    /**
     * Produce lemmas that contradict the given assignment.
     *
     * We can assume that op_constraint is only asserted positive.
     */
    clause_ref op_constraint::produce_lemma(solver& s, assignment const& a, bool is_positive) {
        SASSERT(is_positive);

        if (is_currently_true(a, is_positive))
            return {};

        return produce_lemma(s, a);
    }

    clause_ref op_constraint::produce_lemma(solver& s, assignment const& a) {
        switch (m_op) {
        case code::lshr_op:
            return lemma_lshr(s, a);
        case code::shl_op:
            return lemma_shl(s, a);
        case code::and_op:
            return lemma_and(s, a);
        case code::inv_op:
            return lemma_inv(s, a);
        default:
            NOT_IMPLEMENTED_YET();
            return {};
        }
    }

    void op_constraint::activate(solver& s) {
        switch (m_op) {
        case code::and_op:
            // handle masking of high order bits
            activate_and(s);
            break;
        case code::udiv_op: // division & remainder axioms (as they always occur as pairs; we do this only for divisions)
            activate_udiv(s);
            break;
        default:
            break;
        }
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
     *      q >= N  ->  r = 0
     *      q >= k  ->  r[i] = 0 for N - k <= i < N     (bit indices range from 0 to N-1, inclusive)
     *      q >= k  ->  r <= 2^{N-k} - 1
     *      q = k   ->  r[i] = p[i+k] for 0 <= i < N - k
     *      r <= p
     *      q != 0  ->  r <= p      (subsumed by previous axiom)
     *      q != 0  /\  p > 0 ->  r < p
     *      q = 0   ->  r = p
     *      p = q   ->  r = 0
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
    clause_ref op_constraint::lemma_lshr(solver& s, assignment const& a) {
        auto& m = p().manager();
        auto const pv = a.apply_to(p());
        auto const qv = a.apply_to(q());
        auto const rv = a.apply_to(r());
        unsigned const N = m.power_of_2();

        signed_constraint const lshr(this, true);

        if (pv.is_val() && rv.is_val() && rv.val() > pv.val())
            // r <= p
            return s.mk_clause(~lshr, s.ule(r(), p()), true);
        else if (qv.is_val() && qv.val() >= N && rv.is_val() && !rv.is_zero())
            // TODO: instead of rv.is_val() && !rv.is_zero(), we should use !is_forced_zero(r) which checks whether eval(r) = 0 or bvalue(r=0) = true; see saturation.cpp
            // q >= N -> r = 0
            return s.mk_clause(~lshr, ~s.ule(N, q()), s.eq(r()), true);
        else if (qv.is_zero() && pv.is_val() && rv.is_val() && pv != rv)
            // q = 0 -> p = r
            return s.mk_clause(~lshr, ~s.eq(q()), s.eq(p(), r()), true);
        else if (qv.is_val() && !qv.is_zero() && pv.is_val() && rv.is_val() && !pv.is_zero() && rv.val() >= pv.val())
            // q != 0 & p > 0 -> r < p
            return s.mk_clause(~lshr, s.eq(q()), s.ule(p(), 0), s.ult(r(), p()), true);
        else if (qv.is_val() && !qv.is_zero() && qv.val() < N && rv.is_val() && rv.val() > rational::power_of_two(N - qv.val().get_unsigned()) - 1)
            // q >= k -> r <= 2^{N-k} - 1
            return s.mk_clause(~lshr, ~s.ule(qv.val(), q()), s.ule(r(), rational::power_of_two(N - qv.val().get_unsigned()) - 1), true);
        // else if (pv == qv && !rv.is_zero())
        //     return s.mk_clause(~lshr, ~s.eq(p(), q()), s.eq(r()), true);
        else if (pv.is_val() && rv.is_val() && qv.is_val() && !qv.is_zero()) {
            unsigned k = qv.val().get_unsigned();
            // q = k  ->  r[i] = p[i+k] for 0 <= i < N - k
            for (unsigned i = 0; i < N - k; ++i) {
                if (rv.val().get_bit(i) && !pv.val().get_bit(i + k)) {
                    return s.mk_clause(~lshr, ~s.eq(q(), k), ~s.bit(r(), i), s.bit(p(), i + k), true);
                }
                if (!rv.val().get_bit(i) && pv.val().get_bit(i + k)) {
                    return s.mk_clause(~lshr, ~s.eq(q(), k), s.bit(r(), i), ~s.bit(p(), i + k), true);
                }
            }
        }
        else {
            // forward propagation
            SASSERT(!(pv.is_val() && qv.is_val() && rv.is_val()));
            // LOG(p() << " = " << pv << " and " << q() << " = " << qv << " yields [>>] " << r() << " = " << (qv.val().is_unsigned() ? machine_div2k(pv.val(), qv.val().get_unsigned()) : rational::zero()));
            if (qv.is_val() && !rv.is_val()) {
                rational const& q_val = qv.val();
                if (q_val >= N)
                    // q >= N ==> r = 0
                    return s.mk_clause(~lshr, ~s.ule(N, q()), s.eq(r()), true);
                if (pv.is_val()) {
                    SASSERT(q_val.is_unsigned());
                    // p = p_val & q = q_val ==> r = p_val / 2^q_val
                    rational const r_val = machine_div2k(pv.val(), q_val.get_unsigned());
                    return s.mk_clause(~lshr, ~s.eq(p(), pv), ~s.eq(q(), qv), s.eq(r(), r_val), true);
                }
            }
        }
        return {};
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
            return to_lbool(r.val() == machine_div2k(p.val(), q.val().get_unsigned()));
        }

        // TODO: other cases when we know lower bound of q,
        //       e.g, q = 2^k*q1 + q2, where q2 is a constant.
        return l_undef;
    }

    /**
     * Enforce axioms for constraint: r == p << q
     *
     *      q >= N  ->  r = 0
     *      q >= k  ->  r = 0  \/  r >= 2^k
     *      q >= k  ->  r[i] = 0 for i < k
     *      q = k   ->  r[i+k] = p[i] for 0 <= i < N - k
     *      q = 0   ->  r = p
     */
    clause_ref op_constraint::lemma_shl(solver& s, assignment const& a) {
        auto& m = p().manager();
        auto const pv = a.apply_to(p());
        auto const qv = a.apply_to(q());
        auto const rv = a.apply_to(r());
        unsigned const N = m.power_of_2();

        signed_constraint const shl(this, true);

        if (qv.is_val() && qv.val() >= N && rv.is_val() && !rv.is_zero())
            // q >= N  ->  r = 0
            return s.mk_clause(~shl, ~s.ule(N, q()), s.eq(r()), true);
        else if (qv.is_zero() && pv.is_val() && rv.is_val() && rv != pv)
            // q = 0  ->  r = p
            return s.mk_clause(~shl, ~s.eq(q()), s.eq(r(), p()), true);
        else if (qv.is_val() && !qv.is_zero() && qv.val() < N && rv.is_val() &&
            !rv.is_zero() && rv.val() < rational::power_of_two(qv.val().get_unsigned()))
            // q >= k  ->  r = 0  \/  r >= 2^k  (intuitive version)
            // q >= k  ->  r - 1 >= 2^k - 1     (equivalent unit constraint to better support narrowing)
            return s.mk_clause(~shl, ~s.ule(qv.val(), q()), s.ule(rational::power_of_two(qv.val().get_unsigned()) - 1, r() - 1), true);
        else if (pv.is_val() && rv.is_val() && qv.is_val() && !qv.is_zero()) {
            unsigned k = qv.val().get_unsigned();
            // q = k  ->  r[i+k] = p[i] for 0 <= i < N - k
            for (unsigned i = 0; i < N - k; ++i) {
                if (rv.val().get_bit(i + k) && !pv.val().get_bit(i)) {
                    return s.mk_clause(~shl, ~s.eq(q(), k), ~s.bit(r(), i + k), s.bit(p(), i), true);
                }
                if (!rv.val().get_bit(i + k) && pv.val().get_bit(i)) {
                    return s.mk_clause(~shl, ~s.eq(q(), k), s.bit(r(), i + k), ~s.bit(p(), i), true);
                }
            }
        }
        else {
            // forward propagation
            SASSERT(!(pv.is_val() && qv.is_val() && rv.is_val()));
            // LOG(p() << " = " << pv << " and " << q() << " = " << qv << " yields [<<] " << r() << " = " << (qv.val().is_unsigned() ? rational::power_of_two(qv.val().get_unsigned()) * pv.val() : rational::zero()));
            if (qv.is_val() && !rv.is_val()) {
                rational const& q_val = qv.val();
                if (q_val >= N)
                    // q >= N ==> r = 0
                    return s.mk_clause("shl forward 1", {~shl, ~s.ule(N, q()), s.eq(r())}, true);
                if (pv.is_val()) {
                    SASSERT(q_val.is_unsigned());
                    // p = p_val & q = q_val ==> r = p_val * 2^q_val
                    rational const r_val = pv.val() * rational::power_of_two(q_val.get_unsigned());
                    return s.mk_clause("shl forward 2", {~shl, ~s.eq(p(), pv), ~s.eq(q(), qv), s.eq(r(), r_val)}, true);
                }
            }
        }
        return {};
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

    void op_constraint::activate_and(solver& s) {
        auto x = p(), y = q();
        if (x.is_val())
            std::swap(x, y);
        if (!y.is_val())
            return;
        auto& m = x.manager();
        auto yv = y.val();
        if (!(yv + 1).is_power_of_two())
            return;
        signed_constraint const andc(this, true);
        if (yv == m.max_value())
            s.add_clause(~andc, s.eq(x, r()), false);
        else if (yv == 0)
            s.add_clause(~andc, s.eq(r()), false);
        else {
            unsigned N = m.power_of_2();
            unsigned k = yv.get_num_bits();
            SASSERT(k < N);
            rational exp = rational::power_of_two(N - k);
            s.add_clause(~andc, s.eq(x * exp, r() * exp), false);
            s.add_clause(~andc, s.ule(r(), y), false);  // maybe always activate these constraints regardless?
        }
    }

    /**
     * Produce lemmas for constraint: r == p & q
     * r <= p
     * r <= q
     * p = q => r = p
     * p[i] && q[i] = r[i]
     * p = 2^N - 1 => q = r
     * q = 2^N - 1 => p = r
     * p = 2^k - 1 => r*2^{N - k} = q*2^{N - k}
     * q = 2^k - 1 => r*2^{N - k} = p*2^{N - k}
     * p = 2^k - 1 && r = 0 && q != 0 => q >= 2^k
     * q = 2^k - 1 && r = 0 && p != 0 => p >= 2^k
     */
    clause_ref op_constraint::lemma_and(solver& s, assignment const& a) {
        auto& m = p().manager();
        auto pv = a.apply_to(p());
        auto qv = a.apply_to(q());
        auto rv = a.apply_to(r());

        signed_constraint const andc(this, true); // op_constraints are always true

        // r <= p
        if (pv.is_val() && rv.is_val() && rv.val() > pv.val())
            return s.mk_clause(~andc, s.ule(r(), p()), true);
        // r <= q
        if (qv.is_val() && rv.is_val() && rv.val() > qv.val())
            return s.mk_clause(~andc, s.ule(r(), q()), true);
        // p = q => r = p
        if (pv.is_val() && qv.is_val() && rv.is_val() && pv == qv && rv != pv)
            return s.mk_clause(~andc, ~s.eq(p(), q()), s.eq(r(), p()), true);
        if (pv.is_val() && qv.is_val() && rv.is_val()) {
            // p = -1 => r = q
            if (pv.is_max() && qv != rv)
                return s.mk_clause(~andc, ~s.eq(p(), m.max_value()), s.eq(q(), r()), true);
            // q = -1 => r = p
            if (qv.is_max() && pv != rv)
                return s.mk_clause(~andc, ~s.eq(q(), m.max_value()), s.eq(p(), r()), true);

            unsigned const N = m.power_of_2();
            unsigned pow;
            if ((pv.val() + 1).is_power_of_two(pow)) {
                // p = 2^k - 1 && r = 0 && q != 0 => q >= 2^k
                if (rv.is_zero() && !qv.is_zero() && qv.val() <= pv.val())
                    return s.mk_clause(~andc, ~s.eq(p(), pv), ~s.eq(r()), s.eq(q()), s.ule(pv + 1, q()), true);
                // p = 2^k - 1  ==>  r*2^{N - k} = q*2^{N - k}
                if (rv != qv)
                    return s.mk_clause(~andc, ~s.eq(p(), pv), s.eq(r() * rational::power_of_two(N - pow), q() * rational::power_of_two(N - pow)), true);
            }
            if ((qv.val() + 1).is_power_of_two(pow)) {
                // q = 2^k - 1 && r = 0 && p != 0  ==>  p >= 2^k
                if (rv.is_zero() && !pv.is_zero() && pv.val() <= qv.val())
                    return s.mk_clause(~andc, ~s.eq(q(), qv), ~s.eq(r()), s.eq(p()), s.ule(qv + 1, p()), true);
                // q = 2^k - 1  ==>  r*2^{N - k} = p*2^{N - k}
                if (rv != pv)
                    return s.mk_clause(~andc, ~s.eq(q(), qv), s.eq(r() * rational::power_of_two(N - pow), p() * rational::power_of_two(N - pow)), true);
            }

            for (unsigned i = 0; i < N; ++i) {
                bool pb = pv.val().get_bit(i);
                bool qb = qv.val().get_bit(i);
                bool rb = rv.val().get_bit(i);
                if (rb == (pb && qb))
                    continue;
                if (pb && qb && !rb)
                    return s.mk_clause(~andc, ~s.bit(p(), i), ~s.bit(q(), i), s.bit(r(), i), true);
                else if (!pb && rb)
                    return s.mk_clause(~andc, s.bit(p(), i), ~s.bit(r(), i), true);
                else if (!qb && rb)
                    return s.mk_clause(~andc, s.bit(q(), i), ~s.bit(r(), i), true);
                else
                    UNREACHABLE();
            }
            return {};
        }

        // Propagate r if p or q are 0
        if (pv.is_zero() && !rv.is_zero())  // rv not necessarily fully evaluated
            return s.mk_clause(~andc, s.ule(r(), p()), true);
        if (qv.is_zero() && !rv.is_zero())  // rv not necessarily fully evaluated
            return s.mk_clause(~andc, s.ule(r(), q()), true);
        // p = a && q = b ==> r = a & b
        if (pv.is_val() && qv.is_val() && !rv.is_val()) {
            // Just assign by this very weak justification. It will be strengthened in saturation in case of a conflict
            LOG(p() << " = " << pv << " and " << q() << " = " << qv << " yields [band] " << r() << " = " << bitwise_and(pv.val(), qv.val()));
            return s.mk_clause(~andc, ~s.eq(p(), pv), ~s.eq(q(), qv), s.eq(r(), bitwise_and(pv.val(), qv.val())), true);
        }

        return {};
    }

    /** Evaluate constraint: r == p & q */
    lbool op_constraint::eval_and(pdd const& p, pdd const& q, pdd const& r) {
        if ((p.is_zero() || q.is_zero()) && r.is_zero())
            return l_true;

        if (p.is_val() && q.is_val() && r.is_val())
            return r.val() == bitwise_and(p.val(), q.val()) ? l_true : l_false;

        return l_undef;
    }

    /**
     * Produce lemmas for constraint: r == inv p
     * p = 0   ==>  r = 0
     * r = 0   ==>  p = 0
     * p != 0  ==>  odd(r)
     * parity(p) >= k   ==>  p * r >= 2^k
     * parity(p) < k    ==>  p * r <= 2^k - 1
     * parity(p) < k    ==>  r <= 2^(N - k) - 1     (because r is the smallest pseudo-inverse)
     */
    clause_ref op_constraint::lemma_inv(solver& s, assignment const& a) {
        auto& m = p().manager();
        auto pv = a.apply_to(p());
        auto rv = a.apply_to(r());

        if (eval_inv(pv, rv) == l_true)
            return {};

        signed_constraint const invc(this, true);

        // p = 0  ==>  r = 0
        if (pv.is_zero())
            return s.mk_clause(~invc, ~s.eq(p()), s.eq(r()), true);
        // r = 0  ==>  p = 0
        if (rv.is_zero())
            return s.mk_clause(~invc, ~s.eq(r()), s.eq(p()), true);

        // forward propagation: p assigned  ==>  r = pseudo_inverse(eval(p))
        // TODO: (later) this should be propagated instead of adding a clause
        /*if (pv.is_val() && !rv.is_val())
            return s.mk_clause(~invc, ~s.eq(p(), pv), s.eq(r(), pv.val().pseudo_inverse(m.power_of_2())), true);*/

        if (!pv.is_val() || !rv.is_val())
            return {};

        unsigned parity_pv = pv.val().trailing_zeros();
        unsigned parity_rv = rv.val().trailing_zeros();

        LOG("p: " << p() << " := " << pv << "   parity " << parity_pv);
        LOG("r: " << r() << " := " << rv << "   parity " << parity_rv);

        // p != 0  ==>  odd(r)
        if (parity_rv != 0)
            return s.mk_clause("r = inv p  &  p != 0  ==>  odd(r)", {~invc, s.eq(p()), s.odd(r())}, true);

        pdd prod = p() * r();
        rational prodv = (pv * rv).val();
        if (prodv != rational::power_of_two(parity_pv))
            verbose_stream() << prodv << " " << rational::power_of_two(parity_pv) << " " << parity_pv << " " << pv << " " << rv << "\n";
        unsigned lower = 0, upper = m.power_of_2();
        // binary search for the parity (otw. we would have justifications like "parity_at_most(k) && parity_at_least(k)" for at most "k" widths
        while (lower + 1 < upper) {
            unsigned middle = (upper + lower) / 2;
            LOG("Splitting on " << middle);
            if (parity_pv >= middle) { // parity at least middle
                lower = middle;
                LOG("Its in [" << lower << "; " << upper << ")");
                // parity(p) >= k  ==>  p * r >= 2^k
                if (prodv < rational::power_of_two(middle))
                    return s.mk_clause("r = inv p  &  parity(p) >= k  ==>  p*r >= 2^k",
                        {~invc, ~s.parity_at_least(p(), middle), s.uge(prod, rational::power_of_two(middle))}, false);
                // parity(p) >= k  ==>  r <= 2^(N - k) - 1     (because r is the smallest pseudo-inverse)
                rational const max_rv = rational::power_of_two(m.power_of_2() - middle) - 1;
                if (rv.val() > max_rv)
                    return s.mk_clause("r = inv p  &  parity(p) >= k  ==>  r <= 2^(N - k) - 1",
                        {~invc, ~s.parity_at_least(p(), middle), s.ule(r(), max_rv)}, false);
            }
            else { // parity less than middle
                SASSERT(parity_pv < middle);
                upper = middle;
                LOG("Its in [" << lower << "; " << upper << ")");
                // parity(p) < k   ==>  p * r <= 2^k - 1
                if (prodv > rational::power_of_two(middle))
                    return s.mk_clause("r = inv p  &  parity(p) < k  ==>  p*r <= 2^k - 1",
                        {~invc, s.parity_at_least(p(), middle), s.ule(prod, rational::power_of_two(middle) - 1)}, false);
            }
        }
         // Why did it evaluate to false in this case?
        UNREACHABLE();
        return {};
    }

    /** Evaluate constraint: r == inv p */
    lbool op_constraint::eval_inv(pdd const& p, pdd const& r) {
        if (!p.is_val() || !r.is_val())
            return l_undef;

        if (p.is_zero() || r.is_zero()) // the inverse of 0 is 0 (by arbitrary definition). Just to have some unique value
            return to_lbool(p.is_zero() && r.is_zero());

        return to_lbool(p.val().pseudo_inverse(p.power_of_2()) == r.val());
    }
    
    void op_constraint::activate_udiv(solver& s) {
        // signed_constraint const udivc(this, true); Do we really need this premiss? We anyway assert these constraints as unit clauses

        pdd const& quot = r();
        pdd const& rem = m_linked->r();
        
        // Axioms for quotient/remainder:
        //      a = b*q + r
        //      multiplication does not overflow in b*q
        //      addition does not overflow in (b*q) + r; for now expressed as: r <= bq+r
        //      b ≠ 0  ==>  r < b
        //      b = 0  ==>  q = -1
        // TODO: when a,b become evaluable, can we actually propagate q,r? doesn't seem like it.
        //       Maybe we need something like an op_constraint for better propagation.
        s.add_clause(s.eq(q() * quot + rem - p()), false);
        s.add_clause(~s.umul_ovfl(q(), quot), false);
        // r <= b*q+r
        //  { apply equivalence:  p <= q  <=>  q-p <= -p-1 }
        // b*q <= -r-1
        s.add_clause(s.ule(q() * quot, -rem - 1), false);

        auto c_eq = s.eq(q());
        s.add_clause(c_eq, s.ult(rem, q()), false);
        s.add_clause(~c_eq, s.eq(quot + 1), false);
    }
    
    /**
     * Produce lemmas for constraint: r == p / q
     * q = 0   ==>  r = max_value
     * p = 0   ==>  r = 0 || r = max_value
     * q = 1   ==>  r = p
     */
    clause_ref op_constraint::lemma_udiv(solver& s, assignment const& a) {
        auto& m = p().manager();
        auto pv = a.apply_to(p());
        auto qv = a.apply_to(q());
        auto rv = a.apply_to(r());

        if (eval_udiv(pv, qv, rv) == l_true)
            return {};

        signed_constraint const udivc(this, true);

        if (qv.is_zero() && !rv.is_val())
            return s.mk_clause(~udivc, ~s.eq(q()), s.eq(r(), r().manager().max_value()), true);
        if (pv.is_zero() && !rv.is_val())
            return s.mk_clause(~udivc, ~s.eq(p()), s.eq(r()), s.eq(r(), r().manager().max_value()), true);
        if (qv.is_one()) 
            return s.mk_clause(~udivc, ~s.eq(q(), 1), s.eq(r(), p()), true);
        
        if (pv.is_val() && qv.is_val() && !rv.is_val()) {
            SASSERT(!qv.is_zero());
            // TODO: We could actually propagate an interval. Instead of p = 9 & q = 4 => r = 2 we could do p >= 8 && p < 12 && q = 4 => r = 2
            return s.mk_clause(~udivc, ~s.eq(p(), pv.val()), ~s.eq(q(), qv.val()), s.eq(r(), div(pv.val(), qv.val())), true);
        }
        
        return {};
    }

    /** Evaluate constraint: r == p / q */
    lbool op_constraint::eval_udiv(pdd const& p, pdd const& q, pdd const& r) {
        
        if (q.is_zero() && r.is_val()) {
            return r.val() == r.manager().max_value() ? l_true : l_false;
        }
        if (q.is_one()) {
            if (r == p)
                return l_true;
        }
        
        if (!p.is_val() || !q.is_val() || !r.is_val())
            return l_undef;

        return r.val() == div(p.val(), q.val()) ? l_true : l_false;
    }
    
    /**
     * Produce lemmas for constraint: r == p % q
     * p = 0   ==>  r = 0
     * q = 1   ==>  r = 0
     * q = 0   ==>  r = p
     */
    clause_ref op_constraint::lemma_urem(solver& s, assignment const& a) {
        auto& m = p().manager();
        auto pv = a.apply_to(p());
        auto qv = a.apply_to(q());
        auto rv = a.apply_to(r());

        if (eval_urem(pv, qv, rv) == l_true)
            return {};

        signed_constraint const urem(this, true);

        if (pv.is_zero() && !rv.is_val())
            return s.mk_clause(~urem, ~s.eq(p()), s.eq(r()), true);
        if (qv.is_one() && !rv.is_val())
            return s.mk_clause(~urem, ~s.eq(q(), 1), s.eq(r()), true);
        if (qv.is_zero()) 
            return s.mk_clause(~urem, ~s.eq(q()), s.eq(r(), p()), true);
        
        if (pv.is_val() && qv.is_val() && !rv.is_val()) {
            SASSERT(!qv.is_zero());
            return s.mk_clause(~urem, ~s.eq(p(), pv.val()), ~s.eq(q(), qv.val()), s.eq(r(), mod(pv.val(), qv.val())), true);
        }
        
        return {};
    }

    /** Evaluate constraint: r == p % q */
    lbool op_constraint::eval_urem(pdd const& p, pdd const& q, pdd const& r) {
        
        if (q.is_one() && r.is_val()) {
            return r.val().is_zero() ? l_true : l_false;
        }
        if (q.is_zero()) {
            if (r == p)
                return l_true;
        }
        
        if (!p.is_val() || !q.is_val() || !r.is_val())
            return l_undef;

        return r.val() == mod(p.val(), q.val()) ? l_true : l_false; // mod == rem as we know hat q > 0
    }

    void op_constraint::add_to_univariate_solver(pvar v, solver& s, univariate_solver& us, unsigned dep, bool is_positive) const {
        pdd pv = s.subst(p());
        if (!pv.is_univariate_in(v))
            return;
        pdd qv = s.subst(q());
        if (!qv.is_univariate_in(v))
            return;
        pdd rv = s.subst(r());
        if (!rv.is_univariate_in(v))
            return;
        switch (m_op) {
        case code::lshr_op:
            us.add_lshr(pv.get_univariate_coefficients(), qv.get_univariate_coefficients(), rv.get_univariate_coefficients(), !is_positive, dep);
            break;
        case code::shl_op:
            us.add_shl(pv.get_univariate_coefficients(), qv.get_univariate_coefficients(), rv.get_univariate_coefficients(), !is_positive, dep);
            break;
        case code::and_op:
            us.add_and(pv.get_univariate_coefficients(), qv.get_univariate_coefficients(), rv.get_univariate_coefficients(), !is_positive, dep);
            break;
        case code::inv_op:
            us.add_inv(pv.get_univariate_coefficients(), rv.get_univariate_coefficients(), !is_positive, dep);
            break;
        case code::udiv_op:
            us.add_udiv(pv.get_univariate_coefficients(), qv.get_univariate_coefficients(), rv.get_univariate_coefficients(), !is_positive, dep);
            break;
        case code::urem_op:
            us.add_urem(pv.get_univariate_coefficients(), qv.get_univariate_coefficients(), rv.get_univariate_coefficients(), !is_positive, dep);
            break;
        default:
            NOT_IMPLEMENTED_YET();
            break;
        }
    }

}
