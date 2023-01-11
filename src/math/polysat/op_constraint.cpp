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

#if 0
        if (!propagate_bits(s, is_positive))
            return; // conflict
#endif

        if (clause_ref lemma = produce_lemma(s, s.get_assignment()))
            s.add_clause(*lemma);
        
        if (!s.is_conflict() && is_currently_false(s, is_positive))
            s.set_conflict(signed_constraint(this, is_positive));
    }

    bool op_constraint::propagate_bits(solver& s, bool is_positive) {
        switch (m_op) {
        case code::lshr_op:
            return propagate_bits_lshr(s, is_positive);
        case code::shl_op:
            return propagate_bits_shl(s, is_positive);
        case code::and_op:
            return propagate_bits_and(s, is_positive);
        default:
            NOT_IMPLEMENTED_YET();
            return false;
        }
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
        case code::lshr_op:
            break;
        case code::shl_op:
            // TODO: if shift amount is constant p << k, then add p << k == p*2^k
            break;
        case code::and_op:
            // handle masking of high order bits
            activate_and(s);
            break;
        case code::inv_op:
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
    clause_ref op_constraint::lemma_lshr(solver& s, assignment const& a) {
        auto& m = p().manager();
        auto const pv = a.apply_to(p());
        auto const qv = a.apply_to(q());
        auto const rv = a.apply_to(r());
        unsigned const K = m.power_of_2();

        signed_constraint const lshr(this, true);

        if (pv.is_val() && rv.is_val() && rv.val() > pv.val())
            // r <= p
            return s.mk_clause(~lshr, s.ule(r(), p()), true);
        else if (qv.is_val() && qv.val() >= K && rv.is_val() && !rv.is_zero())
            // q >= K -> r = 0
            return s.mk_clause(~lshr, ~s.ule(K, q()), s.eq(r()), true);
        else if (qv.is_zero() && pv.is_val() && rv.is_val() && pv != rv)
            // q = 0 -> p = r
            return s.mk_clause(~lshr, ~s.eq(q()), s.eq(p(), r()), true);
        else if (qv.is_val() && !qv.is_zero() && pv.is_val() && rv.is_val() && !pv.is_zero() && rv.val() >= pv.val())
            // q != 0 & p > 0 -> r < p
            return s.mk_clause(~lshr, s.eq(q()), s.ule(p(), 0), s.ult(r(), p()), true);
        else if (qv.is_val() && !qv.is_zero() && qv.val() < K && rv.is_val() &&
            rv.val() > rational::power_of_two(K - qv.val().get_unsigned()) - 1)
            // q >= k -> r <= 2^{K-k} - 1
            return s.mk_clause(~lshr, ~s.ule(qv.val(), q()), s.ule(r(), rational::power_of_two(K - qv.val().get_unsigned()) - 1), true);
        else if (pv.is_val() && rv.is_val() && qv.is_val() && !qv.is_zero()) {
            unsigned k = qv.val().get_unsigned();
            // q = k  ->  r[i] = p[i+k] for 0 <= i < K - k
            for (unsigned i = 0; i < K - k; ++i) {
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
            if (qv.is_val() && !rv.is_val()) {
                const rational& qr = qv.val();
                if (qr >= m.power_of_2())
                    return s.mk_clause(~lshr, ~s.ule(m.mk_val(m.power_of_2()), q()), s.eq(r()), true);

                if (rv.is_val()) {
                    const rational& pr = pv.val();
                    return s.mk_clause(~lshr, ~s.eq(p(), m.mk_val(pr)), ~s.eq(q(), m.mk_val(qr)), s.eq(r(), m.mk_val(machine_div(pr, rational::power_of_two(qr.get_unsigned())))), true);
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
            // TODO: use right-shift operation instead of division
            auto divisor = rational::power_of_two(q.val().get_unsigned());
            return to_lbool(r.val() == div(p.val(), divisor));
        }

        // TODO: other cases when we know lower bound of q,
        //       e.g, q = 2^k*q1 + q2, where q2 is a constant.
        return l_undef;
    }

    bool op_constraint::propagate_bits_lshr(solver& s, bool is_positive) {
        // TODO: Implement: copy from the left shift
        // TODO: Implement: negative case
        return true;
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
    clause_ref op_constraint::lemma_shl(solver& s, assignment const& a) {
        auto& m = p().manager();
        auto const pv = a.apply_to(p());
        auto const qv = a.apply_to(q());
        auto const rv = a.apply_to(r());
        unsigned const K = m.power_of_2();

        signed_constraint const shl(this, true);

        if (pv.is_val() && !pv.is_zero() && !pv.is_one() && rv.is_val() && !rv.is_zero() && rv.val() < pv.val())
            // r != 0  ->  r >= p
            // r = 0 \/ r >= p      (equivalent)
            // r-1 >= p-1           (equivalent unit constraint to better support narrowing)
            return s.mk_clause(~shl, s.ule(p() - 1, r() - 1), true);
        else if (qv.is_val() && qv.val() >= K && rv.is_val() && !rv.is_zero())
            // q >= K  ->  r = 0
            return s.mk_clause(~shl, ~s.ule(K, q()), s.eq(r()), true);
        else if (qv.is_zero() && pv.is_val() && rv.is_val() && rv != pv)
            // q = 0  ->  r = p
            return s.mk_clause(~shl, ~s.eq(q()), s.eq(r(), p()), true);
        else if (qv.is_val() && !qv.is_zero() && qv.val() < K && rv.is_val() &&
            !rv.is_zero() && rv.val() < rational::power_of_two(qv.val().get_unsigned()))
            // q >= k  ->  r = 0  \/  r >= 2^k  (intuitive version)
            // q >= k  ->  r - 1 >= 2^k - 1     (equivalent unit constraint to better support narrowing)
            return s.mk_clause(~shl, ~s.ule(qv.val(), q()), s.ule(rational::power_of_two(qv.val().get_unsigned()) - 1, r() - 1), true);
        else if (pv.is_val() && rv.is_val() && qv.is_val() && !qv.is_zero()) {
            unsigned k = qv.val().get_unsigned();
            // q = k  ->  r[i+k] = p[i] for 0 <= i < K - k
            for (unsigned i = 0; i < K - k; ++i) {
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
            if (qv.is_val() && !rv.is_val()) {
                const rational& qr = qv.val();
                if (qr >= m.power_of_2())
                    return s.mk_clause(~shl, ~s.ule(m.mk_val(m.power_of_2()), q()), s.eq(r()), true);

                if (rv.is_val()) {
                    const rational& pr = pv.val();
                    return s.mk_clause(~shl, ~s.eq(p(), m.mk_val(pr)), ~s.eq(q(), m.mk_val(qr)), s.eq(r(), m.mk_val(rational::power_of_two(qr.get_unsigned()) * pr)), true);
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

    bool op_constraint::propagate_bits_shl(solver& s, bool is_positive) {
        // TODO: Implement: negative case
        const tbv_ref& p_val = *s.m_fixed_bits.eval(s, m_p);
        const tbv_ref& q_val = *s.m_fixed_bits.eval(s, m_q);
        const tbv_ref& r_val = *s.m_fixed_bits.eval(s, m_r);
        unsigned sz = m_p.power_of_2();

        auto [shift_min, shift_max] = fixed_bits::min_max(q_val);

        unsigned shift_min_u, shift_max_u;

        if (!shift_min.is_unsigned() || shift_min.get_unsigned() > sz)
            shift_min_u = sz;
        else
            shift_min_u = shift_min.get_unsigned();

        if (!shift_max.is_unsigned() || shift_max.get_unsigned() > sz)
            shift_max_u = sz;
        else
            shift_max_u = shift_max.get_unsigned();

        SASSERT(shift_max_u <= sz);
        SASSERT(shift_min_u <= shift_max_u);
        
        unsigned span = shift_max_u - shift_min_u;

        // Shift by at the value we know q to be at least 
        // TODO: Improve performance; we can reuse the justifications from the previous iteration
        if (shift_min_u > 0) {
            for (unsigned i = 0; i < shift_min_u; i++) {
                if (!s.m_fixed_bits.fix_bit(s, m_r, i, BIT_0, bit_justification_constraint::mk_justify_at_least(s, this, m_q, q_val, rational(i + 1)), true))
                    return false;
            }
        }
        for (unsigned i = shift_min_u; i < sz; i++) {
            unsigned j = 0;
            tbit val = p_val[i - shift_min_u];
            if (val == BIT_z)
                continue;
            
            for (; j < span; j++) {
                if (p_val[i - shift_min_u + 1] != val)
                    break;
            }
            if (j == span) { // all elements we could shift there are equal. We can safely set this value
                // TODO: Relax. Sometimes we can reduce the span if further elements in q are set to the respective value
                if (!s.m_fixed_bits.fix_bit(s, m_r, i, val, bit_justification_constraint::mk_justify_between(s, this, m_q, q_val, shift_min, shift_max), true))
                    return false;
            }
        }
        return true;
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
            unsigned K = m.power_of_2();
            unsigned k = yv.get_num_bits();
            SASSERT(k < K);
            rational exp = rational::power_of_two(K - k);
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
     * p = 2^K - 1 => q = r
     * q = 2^K - 1 => p = r
     * p = 2^k - 1 => r*2^{K - k} = q*2^{K - k}
     * q = 2^k - 1 => r*2^{K - k} = p*2^{K - k}
     * r = 0 && q != 0 & p = 2^k - 1 => q >= 2^k   
     * r = 0 && p != 0 & q = 2^k - 1 => p >= 2^k   
     */
    clause_ref op_constraint::lemma_and(solver& s, assignment const& a) {
        auto& m = p().manager();
        auto pv = a.apply_to(p());
        auto qv = a.apply_to(q());
        auto rv = a.apply_to(r());

        signed_constraint const andc(this, true);

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
            if (pv.val() == m.max_value() && qv != rv)
                return s.mk_clause(~andc, ~s.eq(p(), m.max_value()), s.eq(q(), r()), true);
            // q = -1 => r = p
            if (qv.val() == m.max_value() && pv != rv)
                return s.mk_clause(~andc, ~s.eq(q(), m.max_value()), s.eq(p(), r()), true);

            unsigned K = m.power_of_2();
            // p = 2^k - 1 => r*2^{K - k} = q*2^{K - k}
            // TODO
            // if ((pv.val() + 1).is_power_of_two() ...)

            // q = 2^k - 1 => r*2^{K - k} = p*2^{K - k}

            // r = 0 && q != 0 & p = 2^k - 1 => q >= 2^k   
            if ((pv.val() + 1).is_power_of_two() && rv.val() > pv.val())
                return s.mk_clause(~andc, ~s.eq(r()), ~s.eq(p(), pv.val()), s.eq(q()), s.ult(p(), q()), true);
            // r = 0 && p != 0 & q = 2^k - 1 => p >= 2^k
            if (rv.is_zero() && (qv.val() + 1).is_power_of_two() && pv.val() <= qv.val())
                return s.mk_clause(~andc, ~s.eq(r()), ~s.eq(q(), qv.val()), s.eq(p()),s.ult(q(), p()), true);
            
            for (unsigned i = 0; i < K; ++i) {
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
                return {};
            }
        }
        // Propagate r if p or q are 0
        if (pv.is_zero() && !rv.is_zero())  // rv not necessarily fully evaluated
            return s.mk_clause(~andc, s.ule(r(), p()), true);
        if (qv.is_zero() && !rv.is_zero())  // rv not necessarily fully evaluated
            return s.mk_clause(~andc, s.ule(r(), q()), true);

        if (pv.is_val() && qv.is_val() && !rv.is_val()) {
            const rational& pr = pv.val();
            const rational& qr = qv.val();
            return s.mk_clause(~s.eq(p(), m.mk_val(pr)), ~s.eq(q(), m.mk_val(qr)), s.eq(r(), m.mk_val(bitwise_and(pr, qr))), true);
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

    bool op_constraint::propagate_bits_and(solver& s, bool is_positive) {
        // TODO: Implement: negative case
        LOG_H2("Bit-Propagating: " << m_r << " = (" << m_p << ") & (" << m_q << ")");
        const tbv_ref& p_val = *s.m_fixed_bits.eval(s, m_p);
        const tbv_ref& q_val = *s.m_fixed_bits.eval(s, m_q);
        const tbv_ref& r_val = *s.m_fixed_bits.eval(s, m_r);
        LOG("p: " << m_p << " = " << p_val);
        LOG("q: " << m_q << " = " << q_val);
        LOG("r: " << m_r << " = " << r_val);
        unsigned sz = m_p.power_of_2();

        for (unsigned i = 0; i < sz; i++) {
            tbit bp = p_val[i];
            tbit bq = q_val[i];
            tbit br = r_val[i];
            
            if (bp == BIT_0 || bq == BIT_0) {
                // TODO: In case both are 0 use the one with the lower decision-level and not necessarily p
                if (!s.m_fixed_bits.fix_bit(s, m_r, i, BIT_0, bit_justification_constraint::mk_unary(s, this, { bp == BIT_0 ? m_p : m_q, i }), true))
                    return false;
            }
            else if (bp == BIT_1 && bq == BIT_1) {
                if (!s.m_fixed_bits.fix_bit(s, m_r, i, BIT_1, bit_justification_constraint::mk_binary(s, this, { m_p, i }, { m_q, i }), true))
                    return false;
            }
            else if (br == BIT_1) {
                if (!s.m_fixed_bits.fix_bit(s, m_p, i, BIT_1, bit_justification_constraint::mk_unary(s, this, { m_r, i }), true))
                    return false;
                if (!s.m_fixed_bits.fix_bit(s, m_q, i, BIT_1, bit_justification_constraint::mk_unary(s, this, { m_r, i }), true))
                    return false;
            }
            else if (br == BIT_0) {
                if (bp == BIT_1) {
                    if (!s.m_fixed_bits.fix_bit(s, m_q, i, BIT_1, bit_justification_constraint::mk_binary(s, this, { m_p, i }, { m_r, i }), true))
                        return false;
                }
                else if (bq == BIT_1) {
                    if (!s.m_fixed_bits.fix_bit(s, m_p, i, BIT_1, bit_justification_constraint::mk_binary(s, this, { m_q, i }, { m_r, i }), true))
                        return false;
                }
            }
        }
        return true;
    }
    
    /**
     * Produce lemmas for constraint: r == inv p
     * p = 0 => r = 0
     * r = 0 => p = 0
     * odd(r) -- for now we are looking for the smallest pseudo-inverse (there are 2^parity(p) of them)
     * parity(p) >= k && p * r < 2^k => p * r >= 2^k
     * parity(p) < k && p * r >= 2^k => p * r < 2^k
     */
    clause_ref op_constraint::lemma_inv(solver& s, assignment const& a) {
        auto& m = p().manager();
        auto pv = a.apply_to(p());
        auto rv = a.apply_to(r());

        if (eval_inv(pv, rv) == l_true)
            return {};

        signed_constraint const invc(this, true);

        // p = 0 => r = 0
        if (pv.is_zero())
            return s.mk_clause(~invc, ~s.eq(p()), s.eq(r()), true);
        // r = 0 => p = 0
        if (rv.is_zero())
            return s.mk_clause(~invc, ~s.eq(r()), s.eq(p()), true);

        // p assigned => r = pseudo_inverse(eval(p))
        if (pv.is_val() && !rv.is_val()) {
            return s.mk_clause(~invc, ~s.eq(p(), pv), s.eq(r(), pv.val().pseudo_inverse(m.power_of_2())), true);
        }

        if (!pv.is_val() || !rv.is_val())
            return {};
        
        unsigned parity_pv = pv.val().trailing_zeros();
        unsigned parity_rv = rv.val().trailing_zeros();

        // odd(r)
        if (parity_rv != 0)
            return s.mk_clause(~invc, s.odd(r()), true);
        // parity(p) >= k && p * r < 2^k => p * r >= 2^k
        // parity(p) < k && p * r >= 2^k => p * r < 2^k
        pdd prod = p() * r();
        rational prodv = (pv * rv).val();
        SASSERT(prodv != rational::power_of_two(parity_pv)); // Why did it evaluate to false in this case?
        unsigned lower = 0, upper = p().power_of_2();
        // binary search for the parity
        while (lower + 1 < upper) {
            unsigned middle = (upper + lower) / 2;
            LOG("Splitting on " << middle);
            if (parity_pv >= middle) {
                lower = middle;
                LOG("Its in [" << lower << "; " << upper << ")");
                if (prodv < rational::power_of_two(middle))
                    return s.mk_clause(~invc, ~s.parity_at_least(p(), middle), s.uge(prod, rational::power_of_two(middle)), false);
            }
            else {
                upper = middle;
                LOG("Its in [" << lower << "; " << upper << ")");
                if (prodv >= rational::power_of_two(middle))
                    return s.mk_clause(~invc, s.parity_at_least(p(), middle), s.ult(prod, rational::power_of_two(middle)), false);
            }
        }
        UNREACHABLE();
        return {};
    }
    
    /** Evaluate constraint: r == inv p */
    lbool op_constraint::eval_inv(pdd const& p, pdd const& r) {
        if (!p.is_val() || !r.is_val())
            return l_undef;
        
        if (p.is_zero() || r.is_zero()) // the inverse of 0 is 0 (by arbitrary definition). Just to have some unique value
            return p.is_zero() && r.is_zero() ? l_true : l_false;
            
        return p.val().pseudo_inverse(p.power_of_2()) == r.val() ? l_true : l_false;
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
        default:
            NOT_IMPLEMENTED_YET();
            break;
        }
    }

}
