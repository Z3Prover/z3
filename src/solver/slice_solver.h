/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    slice_solver.h

Abstract:

    Implements a solver that slices assertions based on the query.
    
Author:

    Nikolaj Bjorner (nbjorner) 2024-10-07

--*/
#pragma once

#include "util/params.h"

class solver;
class solver_factory;

solver * mk_slice_solver(solver * s);

