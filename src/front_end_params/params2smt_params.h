/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    params2smt_params.h

Abstract:

    Backward compatibility utilities for parameter setting

Author:

    Leonardo de Moura (leonardo) 2011-05-19.

Revision History:

--*/
#ifndef _PARAMS2SMT_PARAMS_H_
#define _PARAMS2SMT_PARAMS_H_

class params_ref;
struct smt_params;

void params2smt_params(params_ref const & s, smt_params & t);

void smt_params2params(smt_params const & s, params_ref & t);

void solver_smt_params_descrs(param_descrs & r);

#endif
