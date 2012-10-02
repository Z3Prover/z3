/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    params2front_end_params.h

Abstract:

    Backward compatibility utilities for parameter setting

Author:

    Leonardo de Moura (leonardo) 2011-05-19.

Revision History:

--*/
#ifndef _PARAMS2FRONT_END_PARAMS_H_
#define _PARAMS2FRONT_END_PARAMS_H_

class params_ref;
struct front_end_params;

void params2front_end_params(params_ref const & s, front_end_params & t);

void front_end_params2params(front_end_params const & s, params_ref & t);

void solver_front_end_params_descrs(param_descrs & r);

#endif
