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

#if 0
void dyn_ack_params::register_params(ini_params & p) {
    p.register_int_param("dack", 0, 2, reinterpret_cast<int&>(m_dack), 
                         "0 - disable dynamic ackermannization, 1 - expand Leibniz's axiom if a congruence is the root of a conflict, 2 - expand Leibniz's axiom if a congruence is used during conflict resolution.");
    p.register_bool_param("dack_eq", m_dack_eq, "enable dynamic ackermannization for transtivity of equalities");
    p.register_unsigned_param("dack_threshold", m_dack_threshold, "number of times the congruence rule must be used before Leibniz's axiom is expanded");
    p.register_double_param("dack_factor", m_dack_factor, "number of instance per conflict");
    p.register_unsigned_param("dack_gc", m_dack_gc, "Dynamic ackermannization garbage collection frequency (per conflict).");
    p.register_double_param("dack_gc_inv_decay", m_dack_gc_inv_decay);
}
#endif

