/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_ast_vector.cpp

Abstract:
    API for creating AST vectors
    
Author:

    Leonardo de Moura (leonardo) 2012-03-09.

Revision History:

--*/
#include<iostream>
#include"z3.h"
#include"api_log_macros.h"
#include"api_context.h"
#include"api_ast_vector.h"
#include"ast_translation.h"
#include"ast_smt2_pp.h"

extern "C" {

    Z3_ast_vector Z3_API Z3_mk_ast_vector(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_ast_vector(c);
        RESET_ERROR_CODE();
        Z3_ast_vector_ref * v = alloc(Z3_ast_vector_ref, mk_c(c)->m());
        mk_c(c)->save_object(v);
        Z3_ast_vector r       = of_ast_vector(v);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    void Z3_API Z3_ast_vector_inc_ref(Z3_context c, Z3_ast_vector v) {
        Z3_TRY;
        LOG_Z3_ast_vector_inc_ref(c, v);
        RESET_ERROR_CODE();
        to_ast_vector(v)->inc_ref();
        Z3_CATCH;
    }

    void Z3_API Z3_ast_vector_dec_ref(Z3_context c, Z3_ast_vector v) {
        Z3_TRY;
        LOG_Z3_ast_vector_dec_ref(c, v);
        RESET_ERROR_CODE();
        to_ast_vector(v)->dec_ref();
        Z3_CATCH;
    }
    
    unsigned Z3_API Z3_ast_vector_size(Z3_context c, Z3_ast_vector v) {
        Z3_TRY;
        LOG_Z3_ast_vector_size(c, v);
        RESET_ERROR_CODE();
        return to_ast_vector_ref(v).size();
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_ast_vector_get(Z3_context c, Z3_ast_vector v, unsigned i) {
        Z3_TRY;
        LOG_Z3_ast_vector_get(c, v, i);
        RESET_ERROR_CODE();
        if (i >= to_ast_vector_ref(v).size()) {
            SET_ERROR_CODE(Z3_IOB);
            RETURN_Z3(0);
        }
        // Remark: Don't need to invoke save_object.
        ast * r = to_ast_vector_ref(v).get(i);
        RETURN_Z3(of_ast(r));
        Z3_CATCH_RETURN(0);
    }

    void Z3_API Z3_ast_vector_set(Z3_context c, Z3_ast_vector v, unsigned i, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_ast_vector_set(c, v, i, a);
        RESET_ERROR_CODE();
        if (i >= to_ast_vector_ref(v).size()) {
            SET_ERROR_CODE(Z3_IOB);
            return;
        }
        to_ast_vector_ref(v).set(i, to_ast(a));
        Z3_CATCH;
    }

    void Z3_API Z3_ast_vector_resize(Z3_context c, Z3_ast_vector v, unsigned n) {
        Z3_TRY;
        LOG_Z3_ast_vector_resize(c, v, n);
        RESET_ERROR_CODE();
        to_ast_vector_ref(v).resize(n);
        Z3_CATCH;
    }

    void Z3_API Z3_ast_vector_push(Z3_context c, Z3_ast_vector v, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_ast_vector_push(c, v, a);
        RESET_ERROR_CODE();
        to_ast_vector_ref(v).push_back(to_ast(a));
        Z3_CATCH;
    }

    Z3_ast_vector Z3_API Z3_ast_vector_translate(Z3_context c, Z3_ast_vector v, Z3_context t) {
        Z3_TRY;
        LOG_Z3_ast_vector_translate(c, v, t);
        RESET_ERROR_CODE();
        if (c == t) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            RETURN_Z3(0);
        }
        ast_translation translator(mk_c(c)->m(), mk_c(t)->m()); 
        Z3_ast_vector_ref * new_v = alloc(Z3_ast_vector_ref, mk_c(t)->m());
        mk_c(t)->save_object(new_v);
        unsigned sz = to_ast_vector_ref(v).size();
        for (unsigned i = 0; i < sz; i++) {
            ast * new_ast = translator(to_ast_vector_ref(v).get(i));
            new_v->m_ast_vector.push_back(new_ast);
        }
        RETURN_Z3(of_ast_vector(new_v));
        Z3_CATCH_RETURN(0);
    }

    Z3_string Z3_API Z3_ast_vector_to_string(Z3_context c, Z3_ast_vector v) {
        Z3_TRY;
        LOG_Z3_ast_vector_to_string(c, v);
        RESET_ERROR_CODE();
        std::ostringstream buffer;
        buffer << "(ast-vector";
        unsigned sz = to_ast_vector_ref(v).size();
        for (unsigned i = 0; i < sz; i++) {
            buffer << "\n  " << mk_ismt2_pp(to_ast_vector_ref(v).get(i), mk_c(c)->m(), 2);
        }
        buffer << ")";
        return mk_c(c)->mk_external_string(buffer.str());
        Z3_CATCH_RETURN(0);
    }

};
