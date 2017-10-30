/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    subpaving_mpff.cpp

Abstract:

    Subpaving for non-linear arithmetic using mpff numerals.

Author:

    Leonardo de Moura (leonardo) 2012-09-18.

Revision History:

--*/
#include "math/subpaving/subpaving_mpff.h"
#include "math/subpaving/subpaving_t_def.h"

// force template instantiation
template class subpaving::context_t<subpaving::config_mpff>;
