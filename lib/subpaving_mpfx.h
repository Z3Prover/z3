/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    subpaving_mpfx.h

Abstract:

    Subpaving for non-linear arithmetic using mpfx numerals

Author:

    Leonardo de Moura (leonardo) 2012-09-20.

Revision History:

--*/
#ifndef __SUBPAVING_MPFX_H_
#define __SUBPAVING_MPFX_H_

#include"subpaving_t.h"
#include"mpfx.h"

namespace subpaving {

struct config_mpfx {
    typedef mpfx_manager            numeral_manager;
    typedef mpfx_manager::exception exception;

    static void round_to_minus_inf(numeral_manager & m) { m.round_to_minus_inf(); }
    static void round_to_plus_inf(numeral_manager & m) { m.round_to_plus_inf(); }
    static void set_rounding(numeral_manager & m, bool to_plus_inf) { m.set_rounding(to_plus_inf); }

    numeral_manager & m_manager;

    config_mpfx(numeral_manager & m):m_manager(m) {}
    numeral_manager & m() const { return m_manager; }
};

typedef context_t<config_mpfx> context_mpfx;

};

#endif
