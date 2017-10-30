/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_bv_params.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-06.

Revision History:

--*/
#ifndef THEORY_BV_PARAMS_H_
#define THEORY_BV_PARAMS_H_

#include "util/params.h"

enum bv_solver_id {
    BS_NO_BV,
    BS_BLASTER
};

struct theory_bv_params {
    bv_solver_id m_bv_mode;
    bool  m_hi_div0; //!< if true, uses the hardware interpretation for div0, mod0, ... if false, div0, mod0, ... are considered uninterpreted.
    bool         m_bv_reflect;
    bool         m_bv_lazy_le;
    bool         m_bv_cc;
    unsigned     m_bv_blast_max_size;
    bool         m_bv_enable_int2bv2int;
    theory_bv_params(params_ref const & p = params_ref()):
        m_bv_mode(BS_BLASTER),
        m_hi_div0(false),
        m_bv_reflect(true),
        m_bv_lazy_le(false),
        m_bv_cc(false),
        m_bv_blast_max_size(INT_MAX),
        m_bv_enable_int2bv2int(true) {
        updt_params(p);
    }
    
    void updt_params(params_ref const & p);

    void display(std::ostream & out) const;
};

#endif /* THEORY_BV_PARAMS_H_ */

