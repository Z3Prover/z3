/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_tactic.h

Abstract:
    API for creating tactics and goals.
    
Author:

    Leonardo de Moura (leonardo) 2012-03-06.

Revision History:

--*/
#ifndef _API_TACTIC_H_
#define _API_TACTIC_H_

#include"api_goal.h"
#include"tactical.h"

struct Z3_tactic_ref : public api::object {
    tactic_ref   m_tactic;
    virtual ~Z3_tactic_ref() {}
};

struct Z3_probe_ref : public api::object {
    probe_ref    m_probe;
    virtual ~Z3_probe_ref() {}
};

inline Z3_tactic_ref * to_tactic(Z3_tactic g) { return reinterpret_cast<Z3_tactic_ref *>(g); }
inline Z3_tactic of_tactic(Z3_tactic_ref * g) { return reinterpret_cast<Z3_tactic>(g); }
inline tactic * to_tactic_ref(Z3_tactic g) { return g == 0 ? 0 : to_tactic(g)->m_tactic.get(); }

inline Z3_probe_ref * to_probe(Z3_probe g) { return reinterpret_cast<Z3_probe_ref *>(g); }
inline Z3_probe of_probe(Z3_probe_ref * g) { return reinterpret_cast<Z3_probe>(g); }
inline probe * to_probe_ref(Z3_probe g) { return g == 0 ? 0 : to_probe(g)->m_probe.get(); }

struct Z3_apply_result_ref : public api::object {
    goal_ref_buffer      m_subgoals;
    model_converter_ref  m_mc;
    proof_converter_ref  m_pc;
    expr_dependency_ref  m_core;
    Z3_apply_result_ref(ast_manager & m);
    virtual ~Z3_apply_result_ref() {}
};

inline Z3_apply_result_ref * to_apply_result(Z3_apply_result g) { return reinterpret_cast<Z3_apply_result_ref *>(g); }
inline Z3_apply_result of_apply_result(Z3_apply_result_ref * g) { return reinterpret_cast<Z3_apply_result>(g); }

#endif
