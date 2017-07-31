/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    subpaving_mpq.h

Abstract:

    Subpaving for non-linear arithmetic using rationals

Author:

    Leonardo de Moura (leonardo) 2012-07-31.

Revision History:

--*/
#ifndef SUBPAVING_MPQ_H_
#define SUBPAVING_MPQ_H_

#include "math/subpaving/subpaving_t.h"
#include "util/mpq.h"

namespace subpaving {

struct config_mpq {
    typedef unsynch_mpq_manager numeral_manager;
    struct exception {};

    static void round_to_minus_inf(numeral_manager & m) {}
    static void round_to_plus_inf(numeral_manager & m) {}
    static void set_rounding(numeral_manager & m, bool to_plus_info) {}
    numeral_manager & m_manager;
    config_mpq(numeral_manager & m):m_manager(m) {}
    numeral_manager & m() const { return m_manager; }
};

typedef context_t<config_mpq> context_mpq;

};

#endif
