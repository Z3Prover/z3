/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    rational.cpp

Abstract:

    Rational numbers

Author:

    Leonardo de Moura (leonardo) 2006-09-18.

Revision History:

--*/
#include<sstream>
#include"util.h"
#include"rational.h"
#ifdef _WINDOWS
#include<strsafe.h>
#endif

synch_mpq_manager *  rational::g_mpq_manager = 0;
rational             rational::m_zero(0);
rational             rational::m_one(1);
rational             rational::m_minus_one(-1);

void rational::initialize() {
    if (!g_mpq_manager) {
        g_mpq_manager = alloc(synch_mpq_manager);
    }
}

void rational::finalize() {
    dealloc(g_mpq_manager);
    g_mpq_manager = 0;
}

