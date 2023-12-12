/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat multiplication overflow constraint

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2021-12-09

--*/
#include "util/log.h"
#include "sat/smt/polysat/core.h"
#include "sat/smt/polysat/constraints.h"
#include "sat/smt/polysat/assignment.h"
#include "sat/smt/polysat/umul_ovfl_constraint.h"


namespace polysat {

    umul_ovfl_constraint::umul_ovfl_constraint(pdd const& p, pdd const& q):
        m_p(p), m_q(q) {
        simplify();
        vars().append(m_p.free_vars());
        for (auto v : m_q.free_vars())
	        if (!vars().contains(v))
	            vars().push_back(v);

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

    void umul_ovfl_constraint::activate(core& c, bool sign, dependency const& dep) {

    }

    void umul_ovfl_constraint::propagate(core& c, lbool value, dependency const& dep) {
        auto& C = c.cs();
        auto p1 = c.subst(p());
        auto q1 = c.subst(q());
        if (narrow_bound(c, value == l_true, p(), q(), p1, q1, dep))
            return;
        if (narrow_bound(c, value == l_true, q(), p(), q1, p1, dep))
            return;
    }

    /**
     * if p constant, q, propagate inequality
     */
    bool umul_ovfl_constraint::narrow_bound(core& c, bool is_positive, pdd const& p0, pdd const& q0, pdd const& p, pdd const& q, dependency const& d) {
        LOG("p: " << p0 << " := " << p);
        LOG("q: " << q0 << " := " << q);

        if (!p.is_val())
            return false;
        VERIFY(!p.is_zero() && !p.is_one());  // evaluation should catch this case

        rational const& M = p.manager().two_to_N();
        auto& C = c.cs();

        // q_bound
        // = min q . Ovfl(p_val, q)
        // = min q . p_val * q >= M
        // = min q . q >= M / p_val
        // = ceil(M / p_val)
        rational const q_bound = ceil(M / p.val());
        SASSERT(2 <= q_bound && q_bound <= M / 2);
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
            c.add_clause("~Ovfl(p, q) & p <= p_bound ==> q < q_bound", { d, ~C.ule(p0, p_bound), C.ule(q_bound, q0) }, false);
        }
        else {
            // Find lowest bound for p such that q_bound is still correct.
            // p_bound = min p . Ovfl(p, q_bound) = ceil(M / q_bound)
            rational const p_bound = ceil(M / q_bound);
            SASSERT(p_bound <= p.val());
            SASSERT(p_bound * q_bound >= M);
            SASSERT(p_bound * (q_bound - 1) < M);
            // LOG("p_bound: " << p.manager().mk_val(p_bound));
            c.add_clause("~Ovfl(p, q) & p >= p_bound ==> q < q_bound", { d, ~C.ule(p_bound, p0), C.ult(q0, q_bound) }, false);
        }
        return true;
    }


}
