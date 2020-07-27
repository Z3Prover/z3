/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    subpaving_hwf.h

Abstract:

    Subpaving for non-linear arithmetic using hardware floats.

Author:

    Leonardo de Moura (leonardo) 2012-08-06.

Revision History:

--*/
#pragma once

#include "math/subpaving/subpaving_t.h"
#include "util/f2n.h"
#include "util/hwf.h"

namespace subpaving {

struct config_hwf {
    f2n<hwf_manager> & m_manager;
public:
    typedef f2n<hwf_manager>            numeral_manager;
    typedef f2n<hwf_manager>::exception exception;

    static void round_to_minus_inf(numeral_manager & m) { m.round_to_minus_inf(); }
    static void round_to_plus_inf(numeral_manager & m)  { m.round_to_plus_inf(); }
    static void set_rounding(numeral_manager & m, bool to_plus_inf)  { m.set_rounding(to_plus_inf); }
    config_hwf(f2n<hwf_manager> & m):m_manager(m) {}
    f2n<hwf_manager> & m() const { return const_cast<f2n<hwf_manager> &>(m_manager); }
};

class context_hwf : public context_t<config_hwf> {
public:
 context_hwf(reslimit& lim, f2n<hwf_manager> & m, params_ref const & p, small_object_allocator * a):context_t<config_hwf>(lim, config_hwf(m), p, a) {}
};

};

