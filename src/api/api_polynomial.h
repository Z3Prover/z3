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
#ifndef API_POLYNOMIAL_H_
#define API_POLYNOMIAL_H_

#include "math/polynomial/polynomial.h"

namespace api {
    
    class pmanager final {
        unsynch_mpz_manager m_nm;
        polynomial::manager m_pm;
        // TODO: add support for caching expressions -> polynomial and back
    public:
        pmanager(reslimit& lim) : m_pm(lim, m_nm) {}
        ~pmanager() {}
        polynomial::manager & pm() { return m_pm; }
    };

};

#endif
