/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    subpaving_mpf.cpp

Abstract:

    Subpaving for non-linear arithmetic using multi-precision floats.

Author:

    Leonardo de Moura (leonardo) 2012-07-31.

Revision History:

--*/
#include"subpaving_mpf.h"
#include"subpaving_t_def.h"

// force template instantiation
template class subpaving::context_t<subpaving::config_mpf>;
