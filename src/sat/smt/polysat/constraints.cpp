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
        auto* cnstr = alloc(ule_constraint, lhs, rhs);
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
            val = l.manager().max_value() + 1 - l.lo().val();
        return true;
    }

    lbool signed_constraint::eval(assignment& a) const {
        lbool r = m_constraint->eval(a);
        return m_sign ? ~r : r;
    }

    std::ostream& signed_constraint::display(std::ostream& out) const {
        if (m_sign) out << "~";
        return out << *m_constraint;        
    }

    bool signed_constraint::is_currently_true(core& c) const { 
        return eval(c.get_assignment()) == l_true; 
    }

    bool signed_constraint::is_currently_false(core& c) const { 
        return eval(c.get_assignment()) == l_false; 
    }

}
