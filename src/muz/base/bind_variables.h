/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    bind_variables.h

Abstract:

    Utility to find constants that are declard as variables.

Author:

    Nikolaj Bjorner (nbjorner) 9-24-2014

Notes:
    

--*/

#ifndef BIND_VARIABLES_H_
#define BIND_VARIABLES_H_

#include "ast/ast.h"

class bind_variables {
    typedef obj_map<app, var*> var2bound;
    typedef obj_map<expr, expr*> cache_t;
    ast_manager&           m;
    app_ref_vector         m_vars;
    obj_map<expr, expr*>   m_cache;
    var2bound              m_var2bound;
    expr_ref_vector        m_pinned;
    ptr_vector<sort>       m_bound;
    svector<symbol>        m_names;
    ptr_vector<expr>       m_todo;
    ptr_vector<expr>       m_args;

    

    expr_ref abstract(expr* fml, cache_t& cache, unsigned scope);
public:
    bind_variables(ast_manager & m);
    ~bind_variables();
    
    expr_ref operator()(expr* fml, bool is_forall);

    void add_var(app* v);
};

#endif /* BIND_VARIABLES_H_ */
