/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    opt_mux.h

Abstract:
   
    Find mutexes - at most 1 constraints and modify soft constraints and bounds.

Author:

    Nikolaj Bjorner (nbjorner) 2022-04-11

--*/

#pragma once

#include "opt/maxsmt.h"

namespace opt {

    class mux {
        ast_manager&     m;
        solver&          s;

    public:
        mux(solver& s);
        lbool operator()(vector<soft>& soft, rational& bound);
    };
};
