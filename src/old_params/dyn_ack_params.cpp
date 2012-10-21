/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dyn_ack_params.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-05-18.

Revision History:

--*/
#include"dyn_ack_params.h"

void dyn_ack_params::register_params(ini_params & p) {
    p.register_int_param("DACK", 0, 2, reinterpret_cast<int&>(m_dack), 
                         "0 - disable dynamic ackermannization, 1 - expand Leibniz's axiom if a congruence is the root of a conflict, 2 - expand Leibniz's axiom if a congruence is used during conflict resolution.");
    p.register_bool_param("DACK_EQ", m_dack_eq, "enable dynamic ackermannization for transtivity of equalities");
    p.register_unsigned_param("DACK_THRESHOLD", m_dack_threshold, "number of times the congruence rule must be used before Leibniz's axiom is expanded");
    p.register_double_param("DACK_FACTOR", m_dack_factor, "number of instance per conflict");
    p.register_unsigned_param("DACK_GC", m_dack_gc, "Dynamic ackermannization garbage collection frequency (per conflict).");
    p.register_double_param("DACK_GC_INV_DECAY", m_dack_gc_inv_decay);
}


