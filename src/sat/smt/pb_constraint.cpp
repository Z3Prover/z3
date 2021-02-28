/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    ba_constraint.cpp

Abstract:
 
    Interface for constraints.

Author:

    Nikolaj Bjorner (nbjorner) 2017-01-30

--*/

#include "sat/smt/pb_constraint.h"

namespace pb {

    unsigned constraint::fold_max_var(unsigned w) const {
        if (lit() != sat::null_literal) w = std::max(w, lit().var());
        for (unsigned i = 0; i < size(); ++i) w = std::max(w, get_lit(i).var());
        return w;
    }

    std::ostream& operator<<(std::ostream& out, constraint const& cnstr) {
        if (cnstr.lit() != sat::null_literal) out << cnstr.lit() << " == ";
        return cnstr.display(out);
    }

    bool constraint::is_watched(solver_interface const& s, literal lit) const {
        return s.get_wlist(~lit).contains(sat::watched(cindex()));
    }

    void constraint::unwatch_literal(solver_interface& s, literal lit) {
        sat::watched w(cindex());
        s.get_wlist(~lit).erase(w);
        SASSERT(!is_watched(s, lit));
    }

    void constraint::watch_literal(solver_interface& s, literal lit) {
        if (is_pure() && lit == ~this->lit()) return;
        SASSERT(!is_watched(s, lit));
        sat::watched w(cindex());
        s.get_wlist(~lit).push_back(w);
    }

    void constraint::nullify_tracking_literal(solver_interface& s) {
        if (lit() != sat::null_literal) {
            unwatch_literal(s, lit());
            unwatch_literal(s, ~lit());
            nullify_literal();
        }
    }

    bool constraint::well_formed() const {
        uint_set vars;
        if (lit() != sat::null_literal) vars.insert(lit().var());
        for (unsigned i = 0; i < size(); ++i) {
            bool_var v = get_lit(i).var();
            if (vars.contains(v)) return false;
            if (get_coeff(i) > k()) return false;
            vars.insert(v);
        }
        return true;
    }


}
