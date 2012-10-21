/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    model_evaluator_params.cpp

Abstract:

    New parameter setting support for rewriter. 

Author:

    Leonardo (leonardo) 2011-04-22

Notes:

--*/
#include"model_evaluator_params.h"

model_evaluator_params::model_evaluator_params() {
    reset();
}

void model_evaluator_params::reset() {
    m_model_completion = false;
    m_cache            = true;
    m_max_steps        = UINT_MAX;
    m_max_memory       = UINT_MAX;
}

#define PARAM(name) param_names.push_back(name)

void model_evaluator_params::get_params(svector<char const *> & param_names) const {
    PARAM(":model-completion");
    PARAM(":cache");
    PARAM(":max-steps");
    PARAM(":max-memory");
}

#define DESCR(NAME, DR) if (strcmp(name, NAME) == 0) return DR 

char const * model_evaluator_params::get_param_descr(char const * name) const {
    DESCR(":model-completion", "(default: false) assigns an interpretation to symbols that are not intepreted by the model.");
    DESCR(":cache", "(default: true) cache intermediate results.");
    DESCR(":max-steps", "(default: infty) maximum number of steps.");
    DESCR(":max-memory", "(default: infty) maximum amount of memory in megabytes.");
    return 0;
}

#define RBOOL(NAME) if (strcmp(name, NAME) == 0) return CPK_BOOL
#define RUINT(NAME) if (strcmp(name, NAME) == 0) return CPK_UINT

param_kind model_evaluator_params::get_param_kind(char const * name) const {
    RBOOL(":model-completion");
    RBOOL(":cache");
    RUINT(":max-steps");
    RUINT(":max-memory");
    return CPK_INVALID;
}

#define SET(NAME, FIELD) if (strcmp(name, NAME) == 0) { FIELD = value; return true; }

bool model_evaluator_params::set_bool_param(char const * name, bool value) {
    SET(":model-completion", m_model_completion);
    SET(":cache", m_cache);
    return false;
}

bool model_evaluator_params::set_uint_param(char const * name, unsigned value) {
    SET(":max-steps", m_max_steps);
    SET(":max-memory", m_max_memory);
    return false;
}


