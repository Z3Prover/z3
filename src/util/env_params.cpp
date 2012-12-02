/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    env_params.cpp

Abstract:

    Goodies for updating environment parameters.

Author:

    Leonardo (leonardo) 2012-12-01

Notes:

--*/
#include"env_params.h"
#include"params.h"
#include"gparams.h"
#include"util.h"
#include"memory_manager.h"

void env_params::updt_params() {
    params_ref p = gparams::get();
    set_verbosity_level(p.get_uint("verbose", get_verbosity_level()));
    enable_warning_messages(p.get_bool("warning", true));
    memory::set_max_size(p.get_uint("memory_max_size", 0));
}

void env_params::collect_param_descrs(param_descrs & d) {
    d.insert("verbose", CPK_UINT, "be verbose, where the value is the verbosity level", "0");
    d.insert("warning", CPK_BOOL, "enable/disable warning messages", "true");
    d.insert("memory_max_size", CPK_UINT, "set hard upper limit for memory consumption (in megabytes), if 0 then there is no bound.", "0");
}
