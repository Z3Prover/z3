/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_datalog.h

Abstract:
    Datalog API
    old external_relation_context_impl

Author:

    Leonardo de Moura (leonardo) 2012-02-29.

Revision History:

--*/
#ifndef API_DATALOG_H_
#define API_DATALOG_H_

#include"z3.h"
#include"ast.h"
#include"smt_params.h"
#include"smt_kernel.h"
#include"api_util.h"

typedef void (*reduce_app_callback_fptr)(void*, func_decl*, unsigned, expr*const*, expr**);
typedef void (*reduce_assign_callback_fptr)(void*, func_decl*, unsigned, expr*const*, unsigned, expr*const*);

namespace api {
    class fixedpoint_context;
};


struct Z3_fixedpoint_ref : public api::object {
    api::fixedpoint_context *   m_datalog;
    params_ref               m_params;
    Z3_fixedpoint_ref():m_datalog(0) {}
    virtual ~Z3_fixedpoint_ref() { dealloc(m_datalog); }
};

inline Z3_fixedpoint_ref * to_fixedpoint(Z3_fixedpoint s) { return reinterpret_cast<Z3_fixedpoint_ref *>(s); }
inline Z3_fixedpoint of_datalog(Z3_fixedpoint_ref * s) { return reinterpret_cast<Z3_fixedpoint>(s); }
inline api::fixedpoint_context * to_fixedpoint_ref(Z3_fixedpoint s) { return to_fixedpoint(s)->m_datalog; }


#endif
