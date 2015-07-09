/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    user_simplifier_plugin.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-05-22.

Revision History:

--*/
#ifndef USER_SIMPLIFIER_PLUGIN_H_
#define USER_SIMPLIFIER_PLUGIN_H_

#include"simplifier_plugin.h"

typedef bool (*reduce_app_fptr)(void *, func_decl *, unsigned, expr * const *, expr **);
typedef bool (*reduce_eq_fptr)(void *, expr *, expr *, expr **);
typedef bool (*reduce_distinct_fptr)(void *, unsigned, expr * const *, expr **);

class user_simplifier_plugin : public simplifier_plugin {
    void *                    m_owner;
    bool                      m_enabled;
    reduce_app_fptr           m_reduce_app_fptr;
    reduce_eq_fptr            m_reduce_eq_fptr;
    reduce_distinct_fptr      m_reduce_distinct_fptr;

public:
    user_simplifier_plugin(symbol const & fname, ast_manager & m);

    virtual simplifier_plugin * mk_fresh();

    void set_reduce_app_fptr(reduce_app_fptr ptr) {
        m_reduce_app_fptr = ptr;
    }
    
    void set_reduce_eq_fptr(reduce_eq_fptr ptr) {
        m_reduce_eq_fptr = ptr;
    }

    void set_reduce_distinct_fptr(reduce_distinct_fptr ptr) {
        m_reduce_distinct_fptr = ptr;
    }
    
    void enable(bool flag) { m_enabled = flag; }
    
    void set_owner(void * ptr) { m_owner = ptr; }

    virtual bool reduce(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);

    virtual bool reduce_eq(expr * lhs, expr * rhs, expr_ref & result);

    virtual bool reduce_distinct(unsigned num_args, expr * const * args, expr_ref & result);

    virtual void flush_caches();
};

#endif /* USER_SIMPLIFIER_PLUGIN_H_ */

