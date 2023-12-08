/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat multiplication overflow constraint

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2021-12-09

--*/
#include "sat/smt/polysat_constraints.h"
#include "sat/smt/polysat_assignment.h"
#include "sat/smt/polysat_umul_ovfl.h"


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

}
