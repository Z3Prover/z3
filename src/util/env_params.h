/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    env_params.h

Abstract:

    Goodies for updating environment parameters.

Author:

    Leonardo (leonardo) 2012-12-01

Notes:

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

struct env_params {
    static void updt_params();
    static void collect_param_descrs(param_descrs & p);
};

Z3_REGISTER_GLOBAL_PARAMS(env_params, env_params::collect_param_descrs);

