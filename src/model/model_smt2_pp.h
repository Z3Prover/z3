/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    model_smt2_pp.h

Abstract:

    Pretty printer for models using SMT2 format.

Author:

    Leonardo de Moura (leonardo)

Revision History:


--*/
#ifndef _MODEL_SMT2_PP_H_
#define _MODEL_SMT2_PP_H_

#include"cmd_context.h"

void model_smt2_pp(std::ostream & out, cmd_context & ctx, model_core const & m, unsigned indent);
void model_smt2_pp(std::ostream & out, ast_manager & m, model_core const & md, unsigned indent);

#endif
