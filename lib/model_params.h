/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    model_params.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-08-23.

Revision History:

--*/
#ifndef _MODEL_PARAMS_H_
#define _MODEL_PARAMS_H_

#include"ini_file.h"

struct model_params {
    bool m_model_partial;
    bool m_model_hide_unused_partitions;
    bool m_model_compact;
    bool m_model_v1_pp;
    bool m_model_v2_pp;
    bool m_model_completion;
    bool m_model_display_arg_sort;

    model_params():
        m_model_partial(false),
        m_model_hide_unused_partitions(true),
        m_model_compact(false),
        m_model_v1_pp(false),
        m_model_v2_pp(false),
        m_model_completion(false),
        m_model_display_arg_sort(true) {
    }

    void register_params(ini_params & p);
};

#endif /* _MODEL_PARAMS_H_ */

