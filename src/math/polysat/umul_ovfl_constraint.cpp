/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat multiplication overflow constraint

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2021-12-09

--*/
#include "math/polysat/umul_ovfl_constraint.h"
#include "math/polysat/solver.h"

namespace polysat {

    umul_ovfl_constraint::umul_ovfl_constraint(pdd const& p, pdd const& q):
        constraint(ckind_t::umul_ovfl_t), m_p(p), m_q(q) {
        simplify();
        m_vars.append(m_p.free_vars());
        for (auto v : m_q.free_vars())
            if (!m_vars.contains(v))
                m_vars.push_back(v);

    }
    void umul_ovfl_constraint::simplify() {
        if (m_p.is_zero() || m_q.is_zero() || m_p.is_one() || m_q.is_one()) {
            m_q = 0;
            m_p = 0;
            return;
        }
        if (m_p.index() > m_q.index())
            swap(m_p, m_q);
    }

    std::ostream& umul_ovfl_constraint::display(std::ostream& out, lbool status) const {
        switch (status) {
        case l_true: return display(out);
        case l_false: return display(out << "~");
        case l_undef: return display(out << "?");
        }
        return out;
    }

    std::ostream& umul_ovfl_constraint::display(std::ostream& out) const {
        return out << "ovfl*(" << m_p << ", " << m_q << ")";
    }

    lbool umul_ovfl_constraint::eval(pdd const& p, pdd const& q) {
        if (p.is_zero() || q.is_zero() || p.is_one() || q.is_one())
            return l_false;

        if (p.is_val() && q.is_val()) {
            if (p.val() * q.val() > p.manager().max_value())
                return l_true;
            else
                return l_false;
        }
        return l_undef;
    }

    lbool umul_ovfl_constraint::eval() const {
        return eval(p(), q());
    }

    lbool umul_ovfl_constraint::eval(assignment const& a) const {
        return eval(a.apply_to(p()), a.apply_to(q()));
    }

    void umul_ovfl_constraint::narrow(solver& s, bool is_positive, bool first) {
        auto p1 = s.subst(p());
        auto q1 = s.subst(q());

        if (is_always_false(is_positive, p1, q1)) {
            s.set_conflict({ this, is_positive });
            return;
        }
        if (is_always_true(is_positive, p1, q1))
            return;

        if (first)
            activate(s, is_positive);
        
        if (try_viable(s, is_positive, p(), q(), p1, q1))
            return;

        if (narrow_bound(s, is_positive, p(), q(), p1, q1))
            return;
        if (narrow_bound(s, is_positive, q(), p(), q1, p1))
            return;
    }

    void umul_ovfl_constraint::activate(solver& s, bool is_positive) {
        // TODO - remove to enable
        return;        
        if (!is_positive) {
            signed_constraint sc(this, is_positive);
            // ¬Omega(p, q)  ==>  q = 0  \/  p <= p*q
            // ¬Omega(p, q)  ==>  p = 0  \/  q <= p*q
            s.add_clause(~sc, s.eq(q()), s.ule(p(), p()*q()), false);
            s.add_clause(~sc, s.eq(p()), s.ule(q(), p()*q()), false);
        }
    }

    /**
     * if p constant, q, propagate inequality
     */
    bool umul_ovfl_constraint::narrow_bound(solver& s, bool is_positive, pdd const& p0, pdd const& q0, pdd const& p, pdd const& q) {
        LOG("p: " << p0 << " := " << p);
        LOG("q: " << q0 << " := " << q);

        if (!p.is_val())
            return false;
        VERIFY(!p.is_zero() && !p.is_one());  // evaluation should catch this case

        rational const& M = p.manager().two_to_N();

        // q_bound
        // = min q . Ovfl(p_val, q)
        // = min q . p_val * q >= M
        // = min q . q >= M / p_val
        // = ceil(M / p_val)
        rational const q_bound = ceil(M / p.val());
        SASSERT(2 <= q_bound && q_bound <= M/2);
        SASSERT(p.val() * q_bound >= M);
        SASSERT(p.val() * (q_bound - 1) < M);
        // LOG("q_bound: " << q.manager().mk_val(q_bound));

        // We need the following properties for the bounds:
        //
        //      p_bound * (q_bound - 1) < M
        //      p_bound * q_bound >= M
        //
        // With these properties we get:
        //
        //      p <= p_bound & q  < q_bound ==> ~Ovfl(p, q)
        //      p >= p_bound & q >= q_bound ==> Ovfl(p, q)
        //
        // Written as lemmas:
        //
        //       Ovfl(p, q) & p <= p_bound ==> q >= q_bound
        //      ~Ovfl(p, q) & p >= p_bound ==> q <  q_bound
        //
        signed_constraint sc(this, is_positive);
        if (is_positive) {
            // Find largest bound for p such that q_bound is still correct.
            // p_bound = max p . (q_bound - 1)*p < M
            //         = max p . p < M / (q_bound - 1)
            //         = ceil(M / (q_bound - 1)) - 1
            rational const p_bound = ceil(M / (q_bound - 1)) - 1;
            SASSERT(p.val() <= p_bound);
            SASSERT(p_bound * q_bound >= M);
            SASSERT(p_bound * (q_bound - 1) < M);
            // LOG("p_bound: " << p.manager().mk_val(p_bound));
            clause_builder lemma(s, "Ovfl(p, q) & p <= p_bound ==> q >= q_bound");
            lemma.insert_eval(~sc);
            lemma.insert_eval(~s.ule(p0, p_bound));
            lemma.insert(s.ule(q_bound, q0));
            s.add_clause(lemma.build());
        }
        else {
            // Find lowest bound for p such that q_bound is still correct.
            // p_bound = min p . Ovfl(p, q_bound) = ceil(M / q_bound)
            rational const p_bound = ceil(M / q_bound);
            SASSERT(p_bound <= p.val());
            SASSERT(p_bound * q_bound >= M);
            SASSERT(p_bound * (q_bound - 1) < M);
            // LOG("p_bound: " << p.manager().mk_val(p_bound));
            clause_builder lemma(s, "~Ovfl(p, q) & p >= p_bound ==> q < q_bound");
            lemma.insert_eval(~sc);
            lemma.insert_eval(~s.ule(p_bound, p0));
            lemma.insert(s.ult(q0, q_bound));
            s.add_clause(lemma.build());
        }
        return true;
    }

    bool umul_ovfl_constraint::try_viable(solver& s, bool is_positive, pdd const& p0, pdd const& q0, pdd const& p, pdd const& q) {
        LOG("p: " << p0 << " := " << p);
        LOG("q: " << q0 << " := " << q);
        signed_constraint sc(this, is_positive);
        return s.m_viable.intersect(p0, q0, sc);
    }

    unsigned umul_ovfl_constraint::hash() const {
    	return mk_mix(p().hash(), q().hash(), kind());
    }

    bool umul_ovfl_constraint::operator==(constraint const& other) const {
        return other.is_umul_ovfl() && p() == other.to_umul_ovfl().p() && q() == other.to_umul_ovfl().q();
    }

    void umul_ovfl_constraint::add_to_univariate_solver(pvar v, solver& s, univariate_solver& us, unsigned dep, bool is_positive) const {
        pdd p1 = s.subst(p());
        if (!p1.is_univariate_in(v))
            return;
        pdd q1 = s.subst(q());
        if (!q1.is_univariate_in(v))
            return;
        us.add_umul_ovfl(p1.get_univariate_coefficients(), q1.get_univariate_coefficients(), !is_positive, dep);
    }
}
