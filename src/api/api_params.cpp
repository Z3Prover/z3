/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_params.cpp

Abstract:
    API for creating parameter sets.
    
    This is essentially a wrapper for params_ref.
    
Author:

    Leonardo de Moura (leonardo) 2012-03-05.

Revision History:

--*/
#include<iostream>
#include "api/z3.h"
#include "api/api_log_macros.h"
#include "api/api_context.h"
#include "api/api_util.h"
#include "util/params.h"

extern "C" {
    
    Z3_params Z3_API Z3_mk_params(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_params(c);
        RESET_ERROR_CODE();
        Z3_params_ref * p = alloc(Z3_params_ref, *mk_c(c));
        mk_c(c)->save_object(p);
        Z3_params r = of_params(p);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }
    
    /**
       \brief Increment the reference counter of the given parameter set.
    */
    void Z3_API Z3_params_inc_ref(Z3_context c, Z3_params p) {
        Z3_TRY;
        LOG_Z3_params_inc_ref(c, p);
        RESET_ERROR_CODE();
        to_params(p)->inc_ref();
        Z3_CATCH;
    }

    /**
       \brief Decrement the reference counter of the given parameter set.
    */
    void Z3_API Z3_params_dec_ref(Z3_context c, Z3_params p) {
        Z3_TRY;
        LOG_Z3_params_dec_ref(c, p);
        RESET_ERROR_CODE();
        to_params(p)->dec_ref();
        Z3_CATCH;
    }

    /**
       \brief Add a Boolean parameter \c k with value \c v to the parameter set \c p.
    */
    void Z3_API Z3_params_set_bool(Z3_context c, Z3_params p, Z3_symbol k, bool v) {
        Z3_TRY;
        LOG_Z3_params_set_bool(c, p, k, v);
        RESET_ERROR_CODE();
        to_params(p)->m_params.set_bool(norm_param_name(to_symbol(k)).c_str(), v);
        Z3_CATCH;
    }

    /**
       \brief Add a unsigned parameter \c k with value \c v to the parameter set \c p.
    */
    void Z3_API Z3_params_set_uint(Z3_context c, Z3_params p, Z3_symbol k, unsigned v) {
        Z3_TRY;
        LOG_Z3_params_set_uint(c, p, k, v);
        RESET_ERROR_CODE();
        to_params(p)->m_params.set_uint(norm_param_name(to_symbol(k)).c_str(), v);
        Z3_CATCH;
    }

    /**
       \brief Add a double parameter \c k with value \c v to the parameter set \c p.
    */
    void Z3_API Z3_params_set_double(Z3_context c, Z3_params p, Z3_symbol k, double v) {
        Z3_TRY;
        LOG_Z3_params_set_double(c, p, k, v);
        RESET_ERROR_CODE();
        to_params(p)->m_params.set_double(norm_param_name(to_symbol(k)).c_str(), v);
        Z3_CATCH;
    }

    /**
       \brief Add a symbol parameter \c k with value \c v to the parameter set \c p.
    */
    void Z3_API Z3_params_set_symbol(Z3_context c, Z3_params p, Z3_symbol k, Z3_symbol v) {
        Z3_TRY;
        LOG_Z3_params_set_symbol(c, p, k, v);
        RESET_ERROR_CODE();
        to_params(p)->m_params.set_sym(norm_param_name(to_symbol(k)).c_str(), to_symbol(v));
        Z3_CATCH;
    }
    
    /**
       \brief Convert a parameter set into a string. This function is mainly used for printing the
       contents of a parameter set.
    */
    Z3_string Z3_API Z3_params_to_string(Z3_context c, Z3_params p) {
        Z3_TRY;
        LOG_Z3_params_to_string(c, p);
        RESET_ERROR_CODE();
        std::ostringstream buffer;
        to_params(p)->m_params.display(buffer);
        return mk_c(c)->mk_external_string(buffer.str());
        Z3_CATCH_RETURN("");
    }

    void Z3_API Z3_params_validate(Z3_context c, Z3_params p, Z3_param_descrs d) {
        Z3_TRY;
        LOG_Z3_params_validate(c, p, d);
        RESET_ERROR_CODE();
        to_params(p)->m_params.validate(*to_param_descrs_ptr(d));
        Z3_CATCH;
    }

    void Z3_API Z3_param_descrs_inc_ref(Z3_context c, Z3_param_descrs p) {
        Z3_TRY;
        LOG_Z3_param_descrs_inc_ref(c, p);
        RESET_ERROR_CODE();
        to_param_descrs(p)->inc_ref();
        Z3_CATCH;
    }

    void Z3_API Z3_param_descrs_dec_ref(Z3_context c, Z3_param_descrs p) {
        Z3_TRY;
        LOG_Z3_param_descrs_dec_ref(c, p);
        RESET_ERROR_CODE();
        to_param_descrs(p)->dec_ref();
        Z3_CATCH;
    }

    Z3_param_kind Z3_API Z3_param_descrs_get_kind(Z3_context c, Z3_param_descrs p, Z3_symbol n) {
        Z3_TRY;
        LOG_Z3_param_descrs_get_kind(c, p, n);
        RESET_ERROR_CODE();
        param_kind k = to_param_descrs_ptr(p)->get_kind(to_symbol(n));
        switch (k) {
        case CPK_UINT:    return Z3_PK_UINT;
        case CPK_BOOL:    return Z3_PK_BOOL;
        case CPK_DOUBLE:  return Z3_PK_DOUBLE;
        case CPK_STRING:  return Z3_PK_STRING;
        case CPK_SYMBOL:  return Z3_PK_SYMBOL;
        case CPK_INVALID: return Z3_PK_INVALID;
        default:          return Z3_PK_OTHER;
        }
        Z3_CATCH_RETURN(Z3_PK_INVALID);
    }
    
    unsigned Z3_API Z3_param_descrs_size(Z3_context c, Z3_param_descrs p) {
        Z3_TRY;
        LOG_Z3_param_descrs_size(c, p);
        RESET_ERROR_CODE();
        return to_param_descrs_ptr(p)->size();
        Z3_CATCH_RETURN(0);
    }

    Z3_symbol Z3_API Z3_param_descrs_get_name(Z3_context c, Z3_param_descrs p, unsigned i) {
        Z3_TRY;
        LOG_Z3_param_descrs_get_name(c, p, i);
        RESET_ERROR_CODE();
        if (i >= to_param_descrs_ptr(p)->size()) {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            return of_symbol(symbol::null);
        }
        Z3_symbol result = of_symbol(to_param_descrs_ptr(p)->get_param_name(i));
        return result;
        Z3_CATCH_RETURN(of_symbol(symbol::null));
    }

    Z3_string Z3_API Z3_param_descrs_get_documentation(Z3_context c, Z3_param_descrs p, Z3_symbol s) {
        Z3_TRY;
        LOG_Z3_param_descrs_get_documentation(c, p, s);
        RESET_ERROR_CODE();
        char const* result = to_param_descrs_ptr(p)->get_descr(to_symbol(s));
        if (result == nullptr) {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            RETURN_Z3(nullptr);
        }
        return mk_c(c)->mk_external_string(result);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_string Z3_API Z3_param_descrs_to_string(Z3_context c, Z3_param_descrs p) {
        Z3_TRY;
        LOG_Z3_param_descrs_to_string(c, p);
        RESET_ERROR_CODE();
        std::ostringstream buffer;
        buffer << "(";
        unsigned sz = to_param_descrs_ptr(p)->size();
        for (unsigned i = 0; i < sz; i++) {
            if (i > 0) 
                buffer << ", ";
            buffer << to_param_descrs_ptr(p)->get_param_name(i);
        }
        buffer << ")";
        return mk_c(c)->mk_external_string(buffer.str());
        Z3_CATCH_RETURN("");
    }

};
