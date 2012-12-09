/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_polynomial.cpp

Abstract:

    Polynomial manager and caches for the external API.

Author:

    Leonardo de Moura (leonardo) 2012-12-08

Notes:
    
--*/
#include"api_polynomial.h"

namespace api {

    pmanager::pmanager():
        m_pm(m_nm) {
    }

    pmanager::~pmanager() {
    }
    
    void pmanager::set_cancel(bool f) {
        m_pm.set_cancel(f);
    }

};
