/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    basic_simplifier_plugin.h

Abstract:

    Simplifier for the basic family.

Author:

    Leonardo (leonardo) 2008-01-07
    
--*/
#ifndef _BASIC_SIMPLIFIER_PLUGIN_H_
#define _BASIC_SIMPLIFIER_PLUGIN_H_

#include"simplifier_plugin.h"

class bool_rewriter;

/**
   \brief Simplifier for the basic family.
*/
class basic_simplifier_plugin : public simplifier_plugin {
    bool_rewriter * m_rewriter;
public:
    basic_simplifier_plugin(ast_manager & m);
    virtual ~basic_simplifier_plugin();
    bool_rewriter & get_rewriter() { return *m_rewriter; }
    bool eliminate_and() const;
    void set_eliminate_and(bool f);
    void mk_eq(expr * lhs, expr * rhs, expr_ref & result);
    void mk_iff(expr * lhs, expr * rhs, expr_ref & result);
    void mk_xor(expr * lhs, expr * rhs, expr_ref & result);
    void mk_implies(expr * lhs, expr * rhs, expr_ref & result);
    void mk_ite(expr * c, expr * t, expr * e, expr_ref & result);
    void mk_and(unsigned num_args, expr * const * args, expr_ref & result);
    void mk_or(unsigned num_args, expr * const * args, expr_ref & result);
    void mk_and(expr * arg1, expr * arg2, expr_ref & result);
    void mk_or(expr * arg1, expr * arg2, expr_ref & result);
    void mk_and(expr * arg1, expr * arg2, expr * arg3, expr_ref & result);
    void mk_or(expr * arg1, expr * arg2, expr * arg3, expr_ref & result);
    void mk_nand(unsigned num_args, expr * const * args, expr_ref & result);
    void mk_nor(unsigned num_args, expr * const * args, expr_ref & result);
    void mk_nand(expr * arg1, expr * arg2, expr_ref & result);
    void mk_nor(expr * arg1, expr * arg2, expr_ref & result);
    void mk_distinct(unsigned num_args, expr * const * args, expr_ref & result);
    void mk_not(expr * n, expr_ref & result);
    virtual bool reduce(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);
    virtual void enable_ac_support(bool flag);
};

/**
   \brief Functor that compares expressions, but puts the expressions e and f(e) close to each other, where
   f is in family m_fid, and has kind m_dkind;
*/
struct expr_lt_proc {
    family_id  m_fid;
    decl_kind  m_dkind;

    expr_lt_proc(family_id fid = null_family_id, decl_kind k = null_decl_kind):m_fid(fid), m_dkind(k) {}

    unsigned get_id(expr * n) const {
        if (m_fid != null_family_id && is_app_of(n, m_fid, m_dkind))
            return (to_app(n)->get_arg(0)->get_id() << 1) + 1;
        else
            return n->get_id() << 1;
    }

    bool operator()(expr * n1, expr * n2) const {
        return get_id(n1) < get_id(n2);
    }
};

#endif /* _BASIC_SIMPLIFIER_PLUGIN_H_ */
