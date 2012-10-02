/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    parameters.h

Abstract:

    Settings and parameters supplied to pre-processing and solver
    modules.

Author:

    Leonardo de Moura (leonardo) 2006-10-18.
    Nikolaj Bjorner (nbjorner) 2007-02-15

Revision History:
    2007-02-15, nbjorner.
    Hoisted out from simplify_parser.h and core_theory_types.h
    in order to share functionality with SMTLIB and other
    front-ends without bringing in the simplifier and core_theory.

--*/
#ifndef _PARAMETERS_H_
#define _PARAMETERS_H_

#include"sat_params.h"
#include"core_theory_params.h"
#include"front_end_params.h"

#endif
