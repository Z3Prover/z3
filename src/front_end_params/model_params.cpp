/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    model_params.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-08-23.

Revision History:

--*/

#include"model_params.h"

void model_params::register_params(ini_params & p) {
    p.register_bool_param("model_partial", m_model_partial, "enable/disable partial function interpretations", true);
    p.register_bool_param("model_v1", m_model_v1_pp, 
                          "use Z3 version 1.x pretty printer", true);
    p.register_bool_param("model_v2", m_model_v2_pp, 
                          "use Z3 version 2.x (x <= 16) pretty printer", true);
    p.register_bool_param("model_compact", m_model_compact, 
                          "try to compact function graph (i.e., function interpretations that are lookup tables", true);
    p.register_bool_param("model_completion", m_model_completion, 
                          "assigns an interptetation to symbols that do not have one in the current model, when evaluating expressions in the current model", true);

}


