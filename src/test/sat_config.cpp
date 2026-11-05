#include "sat/sat_config.h"
#include "sat/sat_types.h"
#include "util/debug.h"
#include <cstring>

static bool rejects_drat_config(char const* parameter, unsigned value) {
    params_ref params;
    params.set_sym("drat.file", symbol("trace.out"));
    if (strcmp(parameter, "drat.disable") == 0)
        params.set_bool(parameter, value != 0);
    else
        params.set_uint(parameter, value);

    try {
        sat::config config(params);
    }
    catch (sat::sat_param_exception const&) {
        return true;
    }
    return false;
}

void tst_sat_config() {
    ENSURE(rejects_drat_config("threads", 2));
    ENSURE(rejects_drat_config("local_search_threads", 1));
    ENSURE(rejects_drat_config("ddfw.threads", 1));
    ENSURE(rejects_drat_config("drat.disable", 1));

    params_ref params;
    params.set_sym("drat.file", symbol("trace.out"));
    sat::config config(params);
    ENSURE(config.m_drat);

    params_ref threaded_params;
    threaded_params.set_uint("threads", 2);
    sat::config threaded_config(threaded_params);
    ENSURE(!threaded_config.m_drat);
}
