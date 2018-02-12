/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_ast_map.h

Abstract:
    API for creating AST maps
    
Author:

    Leonardo de Moura (leonardo) 2012-03-09.

Revision History:

--*/
#ifndef API_AST_MAP_H_
#define API_AST_MAP_H_

#include "api/api_util.h"
#include "util/obj_hashtable.h"

struct Z3_ast_map_ref : public api::object {
    ast_manager &            m;
    obj_map<ast, ast*> m_map;
    Z3_ast_map_ref(api::context& c, ast_manager & _m): api::object(c), m(_m) {}
    ~Z3_ast_map_ref() override;
};

inline Z3_ast_map_ref * to_ast_map(Z3_ast_map v) { return reinterpret_cast<Z3_ast_map_ref *>(v); }
inline Z3_ast_map of_ast_map(Z3_ast_map_ref * v) { return reinterpret_cast<Z3_ast_map>(v); }
inline obj_map<ast, ast*> & to_ast_map_ref(Z3_ast_map v) { return to_ast_map(v)->m_map; }

#endif
