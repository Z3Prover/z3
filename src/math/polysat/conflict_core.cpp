/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat conflict

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/

#include "math/polysat/conflict_core.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"
#include "math/polysat/log_helper.h"

namespace polysat {

    std::ostream& conflict_core::display(std::ostream& out) const {
        out << "TODO: display conflict_core";
        // depending on sign:   A /\ B /\ C     or     ¬A \/ ¬B \/ ¬C
        return out;
    }

}
