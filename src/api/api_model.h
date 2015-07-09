/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_model.h

Abstract:
    API for models

Author:

    Leonardo de Moura (leonardo) 2012-03-08.

Revision History:

--*/
#ifndef API_MODEL_H_
#define API_MODEL_H_

#include"api_util.h"
#include"model.h"

struct Z3_model_ref : public api::object {
    model_ref  m_model;
    Z3_model_ref() {}
    virtual ~Z3_model_ref() {}
};

inline Z3_model_ref * to_model(Z3_model s) { return reinterpret_cast<Z3_model_ref *>(s); }
inline Z3_model of_model(Z3_model_ref * s) { return reinterpret_cast<Z3_model>(s); }
inline model * to_model_ref(Z3_model s) { return to_model(s)->m_model.get(); }

struct Z3_func_interp_ref : public api::object {
    model_ref     m_model; // must have it to prevent reference to m_func_interp to be killed.
    func_interp * m_func_interp;
    Z3_func_interp_ref(model * m):m_model(m), m_func_interp(0) {}
    virtual ~Z3_func_interp_ref() {}
};

inline Z3_func_interp_ref * to_func_interp(Z3_func_interp s) { return reinterpret_cast<Z3_func_interp_ref *>(s); }
inline Z3_func_interp of_func_interp(Z3_func_interp_ref * s) { return reinterpret_cast<Z3_func_interp>(s); }
inline func_interp * to_func_interp_ref(Z3_func_interp s) { return to_func_interp(s)->m_func_interp; }

struct Z3_func_entry_ref : public api::object {
    model_ref           m_model; // must have it to prevent reference to m_func_entry to be killed.
    func_interp *       m_func_interp;
    func_entry const *  m_func_entry;
    Z3_func_entry_ref(model * m):m_model(m), m_func_interp(0), m_func_entry(0) {}
    virtual ~Z3_func_entry_ref() {}
};

inline Z3_func_entry_ref * to_func_entry(Z3_func_entry s) { return reinterpret_cast<Z3_func_entry_ref *>(s); }
inline Z3_func_entry of_func_entry(Z3_func_entry_ref * s) { return reinterpret_cast<Z3_func_entry>(s); }
inline func_entry const * to_func_entry_ref(Z3_func_entry s) { return to_func_entry(s)->m_func_entry; }


#endif
