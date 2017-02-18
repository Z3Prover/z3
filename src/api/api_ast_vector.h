/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_ast_vector.h

Abstract:
    API for creating AST vectors
    
Author:

    Leonardo de Moura (leonardo) 2012-03-09.

Revision History:

--*/
#ifndef API_AST_VECTOR_H_
#define API_AST_VECTOR_H_

#include"api_util.h"

namespace api {
    class context;
};

struct Z3_ast_vector_ref : public api::object {
    ast_ref_vector  m_ast_vector;
    Z3_ast_vector_ref(api::context& c, ast_manager & m): api::object(c), m_ast_vector(m) {}
    virtual ~Z3_ast_vector_ref() {}
};

inline Z3_ast_vector_ref * to_ast_vector(Z3_ast_vector v) { return reinterpret_cast<Z3_ast_vector_ref *>(v); }
inline Z3_ast_vector of_ast_vector(Z3_ast_vector_ref * v) { return reinterpret_cast<Z3_ast_vector>(v); }
inline ast_ref_vector & to_ast_vector_ref(Z3_ast_vector v) { return to_ast_vector(v)->m_ast_vector; }

#endif
