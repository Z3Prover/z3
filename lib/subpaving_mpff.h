/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    subpaving_mpff.h

Abstract:

    Subpaving for non-linear arithmetic using mpff numerals

Author:

    Leonardo de Moura (leonardo) 2012-09-18.

Revision History:

--*/
#ifndef __SUBPAVING_MPFF_H_
#define __SUBPAVING_MPFF_H_

#include"subpaving_t.h"
#include"mpff.h"

namespace subpaving {

struct config_mpff {
    typedef mpff_manager            numeral_manager;
    typedef mpff_manager::exception exception;

    static void round_to_minus_inf(numeral_manager & m) { m.round_to_minus_inf(); }
    static void round_to_plus_inf(numeral_manager & m) { m.round_to_plus_inf(); }
    static void set_rounding(numeral_manager & m, bool to_plus_inf) { m.set_rounding(to_plus_inf); }

    numeral_manager & m_manager;

    config_mpff(numeral_manager & m):m_manager(m) {}
    numeral_manager & m() const { return m_manager; }
};

typedef context_t<config_mpff> context_mpff;

};

#endif
