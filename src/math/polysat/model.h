/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Polysat partial model

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/polysat/justification.h"
#include "math/polysat/search_state.h"
#include "math/polysat/types.h"

namespace polysat {

    struct model {
        vector<rational>        value;
        vector<justification>   justification;
        assignment_t assignment;
    };

}
