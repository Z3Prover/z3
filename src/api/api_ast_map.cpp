/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_ast_map.cpp

Abstract:
    API for creating AST maps
    
Author:

    Leonardo de Moura (leonardo) 2012-03-09.

Revision History:

--*/
#include<iostream>
#include "api/z3.h"
#include "api/api_log_macros.h"
#include "api/api_context.h"
#include "api/api_ast_map.h"
#include "api/api_ast_vector.h"
#include "ast/ast_smt2_pp.h"
#include "util/dec_ref_util.h"

Z3_ast_map_ref::~Z3_ast_map_ref() {
    dec_ref_key_values(m, m_map);
}

extern "C" {

    Z3_ast_map Z3_API Z3_mk_ast_map(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_ast_map(c);
        RESET_ERROR_CODE();
        Z3_ast_map_ref * m = alloc(Z3_ast_map_ref, *mk_c(c), mk_c(c)->m());
        mk_c(c)->save_object(m);
        Z3_ast_map r       = of_ast_map(m);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }

    void Z3_API Z3_ast_map_inc_ref(Z3_context c, Z3_ast_map m) {
        Z3_TRY;
        LOG_Z3_ast_map_inc_ref(c, m);
        RESET_ERROR_CODE();
        to_ast_map(m)->inc_ref();
        Z3_CATCH;
    }

    void Z3_API Z3_ast_map_dec_ref(Z3_context c, Z3_ast_map m) {
        Z3_TRY;
        LOG_Z3_ast_map_dec_ref(c, m);
        RESET_ERROR_CODE();
        if (m)
            to_ast_map(m)->dec_ref();
        Z3_CATCH;
    }

    bool Z3_API Z3_ast_map_contains(Z3_context c, Z3_ast_map m, Z3_ast k) {
        Z3_TRY;
        LOG_Z3_ast_map_contains(c, m, k);
        RESET_ERROR_CODE();
        return to_ast_map_ref(m).contains(to_ast(k));
        Z3_CATCH_RETURN(false);
    }

    Z3_ast Z3_API Z3_ast_map_find(Z3_context c, Z3_ast_map m, Z3_ast k) {
        Z3_TRY;
        LOG_Z3_ast_map_find(c, m, k);
        RESET_ERROR_CODE();
        obj_map<ast, ast*>::obj_map_entry * entry = to_ast_map_ref(m).find_core(to_ast(k));
        if (entry == nullptr) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            RETURN_Z3(nullptr);
        }
        else {
            ast * r = entry->get_data().m_value;
            RETURN_Z3(of_ast(r));
        }
        Z3_CATCH_RETURN(nullptr);
    }

    void Z3_API Z3_ast_map_insert(Z3_context c, Z3_ast_map m, Z3_ast k, Z3_ast v) {
        Z3_TRY;
        LOG_Z3_ast_map_insert(c, m, k, v);
        RESET_ERROR_CODE();
        ast_manager & mng = to_ast_map(m)->m;
        auto& value = to_ast_map_ref(m).insert_if_not_there(to_ast(k), 0);
        if (!value) {
            // new entry
            mng.inc_ref(to_ast(k));
            mng.inc_ref(to_ast(v));
            value = to_ast(v);            
        }
        else {
            // replacing entry
            mng.inc_ref(to_ast(v));
            mng.dec_ref(value);
            value = to_ast(v);
        }
        Z3_CATCH;
    }

    void Z3_API Z3_ast_map_reset(Z3_context c, Z3_ast_map m) {
        Z3_TRY;
        LOG_Z3_ast_map_reset(c, m);
        RESET_ERROR_CODE();
        dec_ref_key_values(to_ast_map(m)->m, to_ast_map_ref(m));
        SASSERT(to_ast_map_ref(m).empty());
        Z3_CATCH;
    }

    void Z3_API Z3_ast_map_erase(Z3_context c, Z3_ast_map m, Z3_ast k) {
        Z3_TRY;
        LOG_Z3_ast_map_erase(c, m, k);
        RESET_ERROR_CODE();
        ast * v = nullptr;
        if (to_ast_map_ref(m).find(to_ast(k), v)) {
            to_ast_map_ref(m).erase(to_ast(k));
            ast_manager & mng = to_ast_map(m)->m;
            mng.dec_ref(to_ast(k));
            mng.dec_ref(v);
        }
        Z3_CATCH;
    }
    
    unsigned Z3_API Z3_ast_map_size(Z3_context c, Z3_ast_map m) {
        Z3_TRY;
        LOG_Z3_ast_map_size(c, m);
        RESET_ERROR_CODE();
        return to_ast_map_ref(m).size();
        Z3_CATCH_RETURN(0);
    }

    Z3_ast_vector Z3_API Z3_ast_map_keys(Z3_context c, Z3_ast_map m) {
        Z3_TRY;
        LOG_Z3_ast_map_keys(c, m);
        RESET_ERROR_CODE();
        Z3_ast_vector_ref * v = alloc(Z3_ast_vector_ref, *mk_c(c), to_ast_map(m)->m);
        mk_c(c)->save_object(v);
        obj_map<ast, ast*>::iterator it  = to_ast_map_ref(m).begin();
        obj_map<ast, ast*>::iterator end = to_ast_map_ref(m).end();
        for (; it != end; ++it) {
            v->m_ast_vector.push_back(it->m_key);
        }
        Z3_ast_vector r       = of_ast_vector(v);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_string Z3_API Z3_ast_map_to_string(Z3_context c, Z3_ast_map m) {
        Z3_TRY;
        LOG_Z3_ast_map_to_string(c, m);
        RESET_ERROR_CODE();
        std::ostringstream buffer;
        ast_manager & mng = to_ast_map(m)->m;
        buffer << "(ast-map";
        obj_map<ast, ast*>::iterator it  = to_ast_map_ref(m).begin();
        obj_map<ast, ast*>::iterator end = to_ast_map_ref(m).end();
        for (; it != end; ++it) {
            buffer << "\n  (" << mk_ismt2_pp(it->m_key, mng, 3) << "\n   " << mk_ismt2_pp(it->m_value, mng, 3) << ")";
        }
        buffer << ")";
        return mk_c(c)->mk_external_string(buffer.str());
        Z3_CATCH_RETURN(nullptr);
    }

};
