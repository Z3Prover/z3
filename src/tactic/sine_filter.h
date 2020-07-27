/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    sine_filter.h

Abstract:

    Tactic that performs Sine Qua Non premise selection

Author:

    Doug Woos

Revision History:

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_sine_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
    ADD_TACTIC("sine-filter", "eliminate premises using Sine Qua Non", "mk_sine_tactic(m, p)")
*/

