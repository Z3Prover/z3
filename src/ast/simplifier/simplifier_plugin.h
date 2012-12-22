/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    simplifier_plugin.h

Abstract:

    Expression simplifier plugin interface.

Author:

    Leonardo (leonardo) 2008-01-03

--*/

#ifndef __SIMPLIFIER_PLUGIN_H__
#define __SIMPLIFIER_PLUGIN_H__

#include"ast.h"

class simplifier;

void expand_args(unsigned num_args, rational const * mults, expr * const * args, ptr_buffer<expr> & new_args);

/**
   \brief Abstract simplifier for the operators in a given family.
*/
class simplifier_plugin {
protected:
    ast_manager &   m_manager;
    family_id       m_fid;
    bool            m_presimp; // true if simplifier is performing pre-simplification...
    bool            m_reduce_invoked; // true if one of the reduce methods were invoked.

    void set_reduce_invoked() { m_reduce_invoked = true; }

public:
    simplifier_plugin(symbol const & fname, ast_manager & m):m_manager(m), m_fid(m.mk_family_id(fname)), m_presimp(false), m_reduce_invoked(false) {}
    
    bool reduce_invoked() const { return m_reduce_invoked; }

    virtual ~simplifier_plugin() {}
    
    virtual simplifier_plugin * mk_fresh() {
        UNREACHABLE();
        return 0;
    }
    
    /**
       \brief Return in \c result an expression \c e equivalent to <tt>(f args[0] ... args[num_args - 1])</tt>.

       Return true if succeeded.
    */
    virtual bool reduce(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) { set_reduce_invoked(); return false; }

    /**
       \brief Return in \c result an expression \c e equivalent to <tt>(f args[0] ... args[0] ... args[num_args - 1])</tt>.
       Where each args[i] occurs mults[i] times.

       Return true if succeeded.
    */
    virtual bool reduce(func_decl * f, unsigned num_args, rational const * mults, expr * const * args, expr_ref & result);

    /**
       \brief Return in \c result an expression \c e equivalent to <tt>(= lhs rhs)</tt>.

       Return true if succeeded.
    */
    virtual bool reduce_eq(expr * lhs, expr * rhs, expr_ref & result) { set_reduce_invoked(); return false; }
    
    /**
       \brief Return in \c result an expression \c e equivalent to <tt>(distinct args[0] ... args[num_args-1])</tt>.

       Return true if succeeded.
    */
    virtual bool reduce_distinct(unsigned num_args, expr * const * args, expr_ref & result) { set_reduce_invoked(); return false; }
    
    family_id get_family_id() const { return m_fid; }
   
    /**
       \brief Simplifiers may maintain local caches. These caches must be flushed when this method is invoked.
    */
    virtual void flush_caches() { /* do nothing */ }

    ast_manager & get_manager() { return m_manager; }

    void enable_presimp(bool flag) { m_presimp = flag; }

    virtual void enable_ac_support(bool flag) {}
};

#endif
