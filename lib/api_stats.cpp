/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_stats.cpp

Abstract:
    API for browsing statistics

Author:

    Leonardo de Moura (leonardo) 2012-03-07.

Revision History:

--*/
#include<iostream>
#include"z3.h"
#include"api_log_macros.h"
#include"api_context.h"
#include"api_stats.h"

extern "C" {

    Z3_string Z3_API Z3_stats_to_string(Z3_context c, Z3_stats s) {
        Z3_TRY;
        LOG_Z3_stats_to_string(c, s);
        RESET_ERROR_CODE();
        std::ostringstream buffer;
        to_stats_ref(s).display_smt2(buffer);
        std::string result = buffer.str();
        // Hack for removing the trailing '\n'
        result = buffer.str();
        SASSERT(result.size() > 0);
        result.resize(result.size()-1);
        return mk_c(c)->mk_external_string(result);
        Z3_CATCH_RETURN("");
    }

    void Z3_API Z3_stats_inc_ref(Z3_context c, Z3_stats s) {
        Z3_TRY;
        LOG_Z3_stats_inc_ref(c, s);
        RESET_ERROR_CODE();
        to_stats(s)->inc_ref();
        Z3_CATCH;
    }

    void Z3_API Z3_stats_dec_ref(Z3_context c, Z3_stats s) {
        Z3_TRY;
        LOG_Z3_stats_dec_ref(c, s);
        RESET_ERROR_CODE();
        to_stats(s)->dec_ref();
        Z3_CATCH;
    }
    
    unsigned Z3_API Z3_stats_size(Z3_context c, Z3_stats s) {
        Z3_TRY;
        LOG_Z3_stats_size(c, s);
        RESET_ERROR_CODE();
        return to_stats_ref(s).size();
        Z3_CATCH_RETURN(0);
    }

    Z3_string Z3_API Z3_stats_get_key(Z3_context c, Z3_stats s, unsigned idx) {
        Z3_TRY;
        LOG_Z3_stats_get_key(c, s, idx);
        RESET_ERROR_CODE();
        if (idx >= to_stats_ref(s).size()) {
            SET_ERROR_CODE(Z3_IOB);
            return "";
        }
        return to_stats_ref(s).get_key(idx);
        Z3_CATCH_RETURN("");
    }

    Z3_bool Z3_API Z3_stats_is_uint(Z3_context c, Z3_stats s, unsigned idx) {
        Z3_TRY;
        LOG_Z3_stats_is_uint(c, s, idx);
        RESET_ERROR_CODE();
        if (idx >= to_stats_ref(s).size()) {
            SET_ERROR_CODE(Z3_IOB);
            return Z3_FALSE;
        }
        return to_stats_ref(s).is_uint(idx);
        Z3_CATCH_RETURN(0);
    }

    Z3_bool Z3_API Z3_stats_is_double(Z3_context c, Z3_stats s, unsigned idx) {
        Z3_TRY;
        LOG_Z3_stats_is_double(c, s, idx);
        RESET_ERROR_CODE();
        if (idx >= to_stats_ref(s).size()) {
            SET_ERROR_CODE(Z3_IOB);
            return Z3_FALSE;
        }
        return !to_stats_ref(s).is_uint(idx);
        Z3_CATCH_RETURN(Z3_FALSE);
    }
    
    unsigned Z3_API Z3_stats_get_uint_value(Z3_context c, Z3_stats s, unsigned idx) {
        Z3_TRY;
        LOG_Z3_stats_get_uint_value(c, s, idx);
        RESET_ERROR_CODE();
        if (idx >= to_stats_ref(s).size()) {
            SET_ERROR_CODE(Z3_IOB);
            return 0;
        }
        if (!to_stats_ref(s).is_uint(idx)) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return 0;
        }
        return to_stats_ref(s).get_uint_value(idx);
        Z3_CATCH_RETURN(0);
    }

    double Z3_API Z3_stats_get_double_value(Z3_context c, Z3_stats s, unsigned idx) {
        Z3_TRY;
        LOG_Z3_stats_get_double_value(c, s, idx);
        RESET_ERROR_CODE();
        if (idx >= to_stats_ref(s).size()) {
            SET_ERROR_CODE(Z3_IOB);
            return 0.0;
        }
        if (to_stats_ref(s).is_uint(idx)) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return 0.0;
        }
        return to_stats_ref(s).get_double_value(idx);
        Z3_CATCH_RETURN(0.0);
    }

};
