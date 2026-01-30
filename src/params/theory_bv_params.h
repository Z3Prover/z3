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
    // Memory layout optimized: fields grouped by size for minimal padding
    // 4-byte fields first
    unsigned     m_bv_blast_max_size;
    unsigned     m_bv_solver;
    bv_solver_id m_bv_mode;
    
    // This bool must be addressable (flet usage in qe/qe.cpp)
    bool         m_bv_enable_int2bv2int;
    
    // Bitfields for 7 boolean flags (packed into 1 byte, but aligned to 4-byte boundary with above bool)
    unsigned     m_hi_div0 : 1;  //!< if true, uses the hardware interpretation for div0, mod0, ... if false, div0, mod0, ... are considered uninterpreted.
    unsigned     m_bv_reflect : 1;
    unsigned     m_bv_lazy_le : 1;
    unsigned     m_bv_cc : 1;
    unsigned     m_bv_watch_diseq : 1;
    unsigned     m_bv_delay : 1;
    unsigned     m_bv_size_reduce : 1;
    
    theory_bv_params(params_ref const & p = params_ref()) 
        : m_bv_blast_max_size(INT_MAX)
        , m_bv_solver(0)
        , m_bv_mode(bv_solver_id::BS_BLASTER)
        , m_bv_enable_int2bv2int(true)
        , m_hi_div0(0)
        , m_bv_reflect(1)
        , m_bv_lazy_le(0)
        , m_bv_cc(0)
        , m_bv_watch_diseq(0)
        , m_bv_delay(1)
        , m_bv_size_reduce(0)
    {
        updt_params(p);
    }
    
    void updt_params(params_ref const & p);

    void display(std::ostream & out) const;
};

// Verify struct packing optimization
// Previous size was 20 bytes, optimized to 16 bytes (4 bytes / 20% reduction)
static_assert(sizeof(theory_bv_params) <= 16, "theory_bv_params size regression - check field ordering and alignment");

