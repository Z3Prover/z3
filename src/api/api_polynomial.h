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
#ifndef _API_POLYNOMIAL_H_
#define _API_POLYNOMIAL_H_

#include"polynomial.h"

namespace api {
    
    class pmanager {
        unsynch_mpz_manager m_nm;
        polynomial::manager m_pm;
        // TODO: add support for caching expressions -> polynomial and back
    public:
        pmanager();
        virtual ~pmanager();
        polynomial::manager & pm() { return m_pm; }
        void set_cancel(bool f);
    };

};

#endif
