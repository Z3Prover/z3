/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Polysat inequalities

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6



--*/
#include "sat/smt/polysat/core.h"
#include "sat/smt/polysat/inequality.h"
#include "sat/smt/polysat/ule_constraint.h"


namespace polysat {


    inequality inequality::from_ule(core& c, constraint_id id) {
        auto src = c.get_constraint(id);
        ule_constraint const& ule = src.to_ule();
        if (src.is_positive())
            return inequality(c, id, ule.unfold_lhs(), ule.unfold_rhs(), src);
        else
            return inequality(c, id, ule.unfold_rhs(), ule.unfold_lhs(), src);
    }


    dependency inequality::dep() const {
        return c.get_dependency(id());
    }

    bool inequality::is_l_v(pdd const& v, signed_constraint const& sc) {
        return sc.is_ule() && v == (sc.sign() ? sc.to_ule().unfold_rhs() : sc.to_ule().unfold_lhs());
    }

    bool inequality::is_g_v(pdd const& v, signed_constraint const& sc) {
        return sc.is_ule() && v == (sc.sign() ? sc.to_ule().unfold_lhs() : sc.to_ule().unfold_rhs());
    }

}
