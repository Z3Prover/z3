/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    subpaving_mpq.cpp

Abstract:

    Subpaving for non-linear arithmetic using rationals.

Author:

    Leonardo de Moura (leonardo) 2012-07-31.

Revision History:

--*/
#include "math/subpaving/subpaving_mpq.h"
#include "math/subpaving/subpaving_t_def.h"

// force template instantiation
template class subpaving::context_t<subpaving::config_mpq>;
