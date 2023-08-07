/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat justification

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/

#include "math/polysat/justification.h"

namespace polysat {

    std::ostream& justification::display(std::ostream& out) const {
        switch (kind()) {
        case justification_k::unassigned:
            return out << "unassigned";
        case justification_k::decision:
            return out << "decision @ " << level();
        case justification_k::propagation_by_viable:
            return out << "propagation by viable @ " << level();
        case justification_k::propagation_by_slicing:
            return out << "propagation by slicing @ " << level();
        }
        UNREACHABLE();
        return out;
    }

}
