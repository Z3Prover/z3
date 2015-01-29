/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_register_engine.cpp

Abstract:

    Class for creating Datalog engines.

Author:

    Nikolaj Bjorner (nbjorner) 2013-08-28

Revision History:

--*/
#include "dl_register_engine.h"
#include "dl_bmc_engine.h"
#include "clp_context.h"
#include "tab_context.h"
#include "rel_context.h"
#include "pdr_dl_interface.h"
#include "ddnf.h"
#include "duality_dl_interface.h"

namespace datalog {
    register_engine::register_engine(): m_ctx(0) {}
    
    engine_base* register_engine::mk_engine(DL_ENGINE engine_type) {
        switch(engine_type) {
        case PDR_ENGINE:
        case QPDR_ENGINE:
            return alloc(pdr::dl_interface, *m_ctx);
        case DATALOG_ENGINE:
            return alloc(rel_context, *m_ctx);
        case BMC_ENGINE:
        case QBMC_ENGINE:
            return alloc(bmc, *m_ctx);
        case TAB_ENGINE:
            return alloc(tab, *m_ctx);
        case CLP_ENGINE:
            return alloc(clp, *m_ctx);
        case DUALITY_ENGINE:
            return alloc(Duality::dl_interface, *m_ctx);
        case DDNF_ENGINE:
            return alloc(ddnf, *m_ctx);
        case LAST_ENGINE:
            UNREACHABLE();
            return 0;
        }
        UNREACHABLE();
        return 0;
    }

}
