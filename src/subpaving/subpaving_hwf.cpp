/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    subpaving_hwf.cpp

Abstract:

    Subpaving for non-linear arithmetic using hardware floats.

Author:

    Leonardo de Moura (leonardo) 2012-08-06.

Revision History:

--*/
#include"subpaving_hwf.h"
#include"subpaving_t_def.h"

// force template instantiation
template class subpaving::context_t<subpaving::config_hwf>;
