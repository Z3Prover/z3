/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    normalize_vars.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-16.

Revision History:

--*/
#ifndef _NORMALIZE_VARS_H_
#define _NORMALIZE_VARS_H_

#include"ast.h"
#include"obj_hashtable.h"

class normalize_vars {
    ast_manager &    m_manager;
    var_ref_vector   m_new_vars;
    unsigned         m_next_var;
    ptr_vector<var>  m_map;
    typedef obj_map<expr, expr *> cache;
    cache            m_cache;
    ptr_vector<expr> m_todo;
    ptr_vector<expr> m_new_children;
public:
    normalize_vars(ast_manager & m):
        m_manager(m),
        m_new_vars(m) {
    }

    expr * operator()(expr * n);
    void reset();
    unsigned get_num_vars() const { return m_new_vars.size(); }
    var * const * get_vars() const { return m_new_vars.c_ptr(); }
};

#endif /* _NORMALIZE_VARS_H_ */

