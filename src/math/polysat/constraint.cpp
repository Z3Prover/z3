/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat constraints

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19

--*/

#include "math/polysat/constraint.h"

namespace polysat {

    std::ostream& constraint::display(std::ostream& out) const {
        switch (kind()) {
        case ckind_t::eq_t:
            return out << p() << " == 0";
        case ckind_t::ule_t:
            return out << lhs() << " <=u " << rhs();
        case ckind_t::sle_t:
            return out << lhs() << " <=s " << rhs();
        }
        return out;
    }

}
