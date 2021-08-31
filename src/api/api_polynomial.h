/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_polynomial.h

Abstract:

    Polynomial manager and caches for the external API.

Author:

    Leonardo de Moura (leonardo) 2012-12-08

Notes:
    
--*/
#pragma once

#include "math/polynomial/polynomial.h"

namespace api {
    
    class pmanager final {
        unsynch_mpz_manager m_nm;
        polynomial::manager m_pm;
        // TODO: add support for caching expressions -> polynomial and back
    public:
        pmanager(reslimit& lim) : m_pm(lim, m_nm) {}
        polynomial::manager & pm() { return m_pm; }
    };

}
