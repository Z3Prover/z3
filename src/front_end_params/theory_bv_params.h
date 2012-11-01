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
#ifndef _THEORY_BV_PARAMS_H_
#define _THEORY_BV_PARAMS_H_

#include"ini_file.h"

enum bv_solver_id {
    BS_NO_BV,
    BS_BLASTER
};

struct theory_bv_params {
    bv_solver_id m_bv_mode;
    bool         m_bv_reflect;
    bool         m_bv_lazy_le;
    bool         m_bv_cc;
    unsigned     m_bv_blast_max_size;
    bool         m_bv_enable_int2bv2int;
    theory_bv_params():
        m_bv_mode(BS_BLASTER),
        m_bv_reflect(true),
        m_bv_lazy_le(false),
        m_bv_cc(false),
        m_bv_blast_max_size(INT_MAX),
        m_bv_enable_int2bv2int(false) {}
     void register_params(ini_params & p) {
         p.register_int_param("BV_SOLVER", 0, 2, reinterpret_cast<int&>(m_bv_mode), "0 - no bv, 1 - simple");
         p.register_unsigned_param("BV_BLAST_MAX_SIZE", m_bv_blast_max_size, "Maximal size for bit-vectors to blast");
         p.register_bool_param("BV_REFLECT", m_bv_reflect);
         p.register_bool_param("BV_LAZY_LE", m_bv_lazy_le);
         p.register_bool_param("BV_CC", m_bv_cc, "enable congruence closure for BV operators");
         p.register_bool_param("BV_ENABLE_INT2BV_PROPAGATION", m_bv_enable_int2bv2int, 
                               "enable full (potentially expensive) propagation for int2bv and bv2int");
     }
};

#endif /* _THEORY_BV_PARAMS_H_ */

