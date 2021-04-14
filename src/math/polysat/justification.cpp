/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat justification

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19

--*/

#include "math/polysat/justification.h"

namespace polysat {

    std::ostream& justification::display(std::ostream& out) const {
        switch (kind()) {
        case justification_k::unassigned:
            return out << "unassigned";
        case justification_k::decision:
            return out << "decision (level " << level() << ")";
        case justification_k::propagation:
            return out << "propagation (level " << level() << ")";
        }
    }

}
