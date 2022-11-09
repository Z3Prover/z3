/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat constraints

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/

#include "math/polysat/constraint.h"
#include "math/polysat/clause.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"
#include "math/polysat/log_helper.h"
#include "math/polysat/ule_constraint.h"
#include "math/polysat/umul_ovfl_constraint.h"
#include "math/polysat/smul_fl_constraint.h"
#include "math/polysat/op_constraint.h"

namespace polysat {

    bool signed_constraint::is_eq() const {
        return is_positive() && m_constraint->is_eq();
    }

    pdd const& signed_constraint::eq() const {
        SASSERT(is_eq());
        return m_constraint->to_ule().lhs();
    }

    signed_constraint inequality::as_signed_constraint() const {
        return signed_constraint(const_cast<constraint*>(src), !is_strict);
    }

    ule_constraint& constraint::to_ule() {
        return *dynamic_cast<ule_constraint*>(this);
    }

    ule_constraint const& constraint::to_ule() const {
        return *dynamic_cast<ule_constraint const*>(this);
    }

    umul_ovfl_constraint& constraint::to_umul_ovfl() {
        return *dynamic_cast<umul_ovfl_constraint*>(this);
    }

    umul_ovfl_constraint const& constraint::to_umul_ovfl() const {
        return *dynamic_cast<umul_ovfl_constraint const*>(this);
    }

    smul_fl_constraint& constraint::to_smul_fl() {
        return *dynamic_cast<smul_fl_constraint*>(this);
    }

    smul_fl_constraint const& constraint::to_smul_fl() const {
        return *dynamic_cast<smul_fl_constraint const*>(this);
    }

    op_constraint& constraint::to_op() {
        return *dynamic_cast<op_constraint*>(this);
    }

    op_constraint const& constraint::to_op() const {
        return *dynamic_cast<op_constraint const*>(this);
    }

    std::string constraint::bvar2string() const {
        std::stringstream out;
        out << " (b";
        if (has_bvar()) { out << bvar(); } else { out << "_"; }
        out << ")";
        return out.str();
    }

    lbool signed_constraint::bvalue(solver& s) const {
        return get()->has_bvar() ? s.m_bvars.value(blit()) : l_undef;
    }

    std::ostream& constraint_pp::display(std::ostream& out) const {
        if (c)
            return c->display(out, status);
        else
            return out << "<null>";
    }

}
