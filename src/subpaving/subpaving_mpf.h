/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    subpaving_mpf.h

Abstract:

    Subpaving for non-linear arithmetic using multi-precision floats.

Author:

    Leonardo de Moura (leonardo) 2012-07-31.

Revision History:

--*/
#ifndef __SUBPAVING_MPF_H_
#define __SUBPAVING_MPF_H_

#include"subpaving_t.h"
#include"mpf.h"
#include"f2n.h"

namespace subpaving {

struct config_mpf {
    f2n<mpf_manager> & m_manager;
public:
    typedef f2n<mpf_manager>            numeral_manager;
    typedef mpf                         numeral;
    typedef f2n<mpf_manager>::exception exception;

    static void round_to_minus_inf(numeral_manager & m) { m.round_to_minus_inf(); }
    static void round_to_plus_inf(numeral_manager & m)  { m.round_to_plus_inf(); }
    static void set_rounding(numeral_manager & m, bool to_plus_inf)  { m.set_rounding(to_plus_inf); }
    config_mpf(f2n<mpf_manager> & m):m_manager(m) {}
    f2n<mpf_manager> & m() const { return const_cast<f2n<mpf_manager> &>(m_manager); }
};

class context_mpf : public context_t<config_mpf> {
public:
    context_mpf(f2n<mpf_manager> & m, params_ref const & p, small_object_allocator * a):context_t<config_mpf>(config_mpf(m), p, a) {}
};

};

#endif
