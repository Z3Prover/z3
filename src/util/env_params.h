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
#ifndef ENV_PARAMS_H_
#define ENV_PARAMS_H_

class param_descrs;

struct env_params {
    static void updt_params();
    static void collect_param_descrs(param_descrs & p);
    /*
      REG_PARAMS('env_params::collect_param_descrs')
    */
};

#endif
