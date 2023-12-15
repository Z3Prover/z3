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
#pragma once

#include "util/params.h"

enum bv_solver_id {
    BS_NO_BV,
    BS_BLASTER
};

struct theory_bv_params {
    bv_solver_id m_bv_mode = bv_solver_id::BS_BLASTER;
    bool         m_hi_div0 = false; //!< if true, uses the hardware interpretation for div0, mod0, ... if false, div0, mod0, ... are considered uninterpreted.
    bool         m_bv_reflect = true;
    bool         m_bv_lazy_le = false;
    bool         m_bv_cc = false;
    unsigned     m_bv_blast_max_size = INT_MAX;
    bool         m_bv_enable_int2bv2int = true;
    bool         m_bv_watch_diseq = false;
    bool         m_bv_delay = true;
    bool         m_bv_size_reduce = false;
    unsigned     m_bv_solver = 0;
    theory_bv_params(params_ref const & p = params_ref()) {
        updt_params(p);
    }
    
    void updt_params(params_ref const & p);

    void display(std::ostream & out) const;
};


