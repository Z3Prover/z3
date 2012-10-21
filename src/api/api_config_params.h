/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_config_params.h

Abstract:
    Configuration parameters

Author:

    Leonardo de Moura (leonardo) 2012-02-29.

Revision History:

--*/
#ifndef _API_CONFIG_PARAMS_H_
#define _API_CONFIG_PARAMS_H_

#include"ini_file.h"
#include"front_end_params.h"

namespace api {

    class config_params {
    public:
        ini_params       m_ini;
        front_end_params m_params;
        config_params();
        config_params(front_end_params const & p);
    };

};

#endif
