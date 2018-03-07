/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_register_engine.h

Abstract:

    Class for creating Datalog engines.

Author:

    Nikolaj Bjorner (nbjorner) 2013-08-28

Revision History:

--*/
#ifndef DL_REGISTER_ENGINE_H_
#define DL_REGISTER_ENGINE_H_

#include "muz/base/dl_context.h"

namespace datalog {

    class register_engine : public register_engine_base {
        context* m_ctx;
    public:
        register_engine();
        engine_base* mk_engine(DL_ENGINE engine_type) override;
        void set_context(context* ctx) override { m_ctx = ctx; }
    };

}

#endif
