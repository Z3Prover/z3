/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    basic_simplifier_plugin.cpp

Abstract:

    Simplifier for the basic family.

Author:

    Leonardo (leonardo) 2008-01-07
    
--*/
#include"basic_simplifier_plugin.h"
#include"ast_ll_pp.h"
#include"bool_rewriter.h"

basic_simplifier_plugin::basic_simplifier_plugin(ast_manager & m):
    simplifier_plugin(symbol("basic"), m), 
    m_rewriter(alloc(bool_rewriter, m)) {
}

basic_simplifier_plugin::~basic_simplifier_plugin() {
    dealloc(m_rewriter);
}
    
bool basic_simplifier_plugin::reduce(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    set_reduce_invoked();
    SASSERT(f->get_family_id() == m_manager.get_basic_family_id());
    basic_op_kind k = static_cast<basic_op_kind>(f->get_decl_kind());
    switch (k) {
    case OP_FALSE:     
    case OP_TRUE:      
        return false;
    case OP_EQ:        
        SASSERT(num_args == 2); 
        mk_eq(args[0], args[1], result); 
        return true;
    case OP_DISTINCT:
        mk_distinct(num_args, args, result);
        return true;
    case OP_ITE: 
        SASSERT(num_args == 3);
        mk_ite(args[0], args[1], args[2], result);
        return true;
    case OP_AND:       
        mk_and(num_args, args, result); 
        return true;
    case OP_OR:        
        mk_or(num_args, args, result); 
        return true;
    case OP_IMPLIES:
        mk_implies(args[0], args[1], result); 
        return true;
    case OP_IFF:      
        mk_iff(args[0], args[1], result); 
        return true;
    case OP_XOR: 
        mk_xor(args[0], args[1], result); 
        return true;
    case OP_NOT:      
        SASSERT(num_args == 1);
        mk_not(args[0], result); 
        return true;
    default:
        UNREACHABLE();
        return false;
    }
}

/**
   \brief Return true if \c rhs is of the form (ite c t1 t2) and are_distinct(lhs, t1) and are_distinct(lhs, t2).
*/
static bool is_lhs_diseq_rhs_ite_branches(ast_manager & m, expr * lhs, expr * rhs) {
    return m.is_ite(rhs) && m.are_distinct(lhs, to_app(rhs)->get_arg(1)) && m.are_distinct(lhs, to_app(rhs)->get_arg(2));
}

/**
   \brief Return true if \c rhs is of the form (ite c t1 t2) and lhs = t1 && are_distinct(lhs, t2)
*/
static bool is_lhs_eq_rhs_ite_then(ast_manager & m, expr * lhs, expr * rhs) {
    return m.is_ite(rhs) && lhs == to_app(rhs)->get_arg(1) && m.are_distinct(lhs, to_app(rhs)->get_arg(2));
}

/**
   \brief Return true if \c rhs is of the form (ite c t1 t2) and are_distinct(lhs,t1) && lhs = t2
*/
static bool is_lhs_eq_rhs_ite_else(ast_manager & m, expr * lhs, expr * rhs) {
    return m.is_ite(rhs) && lhs == to_app(rhs)->get_arg(2) && m.are_distinct(lhs, to_app(rhs)->get_arg(1));
}

void basic_simplifier_plugin::mk_eq(expr * lhs, expr * rhs, expr_ref & result) {
    // (= t1 (ite C t2 t3)) --> false if are_distinct(t1, t2) && are_distinct(t1, t3)
    if (is_lhs_diseq_rhs_ite_branches(m_manager, lhs, rhs) || is_lhs_diseq_rhs_ite_branches(m_manager, rhs, lhs)) {
        result = m_manager.mk_false();
    }
    // (= t1 (ite C t2 t3)) --> C if t1 = t2 && are_distinct(t1, t3)
    else if (is_lhs_eq_rhs_ite_then(m_manager, lhs, rhs)) {
        result = to_app(rhs)->get_arg(0);
    }
    // (= t1 (ite C t2 t3)) --> C if t1 = t2 && are_distinct(t1, t3)
    else if (is_lhs_eq_rhs_ite_then(m_manager, rhs, lhs)) {
        result = to_app(lhs)->get_arg(0);
    }
    // (= t1 (ite C t2 t3)) --> (not C)  if t1 = t3 && are_distinct(t1, t2)
    else if (is_lhs_eq_rhs_ite_else(m_manager, lhs, rhs)) {
        mk_not(to_app(rhs)->get_arg(0), result);
    }
    // (= t1 (ite C t2 t3)) --> (not C)  if t1 = t3 && are_distinct(t1, t2)
    else if (is_lhs_eq_rhs_ite_else(m_manager, rhs, lhs)) {
        mk_not(to_app(lhs)->get_arg(0), result);
    }
    else {
        m_rewriter->mk_eq(lhs, rhs, result);
    }
}

bool basic_simplifier_plugin::eliminate_and() const { return m_rewriter->elim_and(); }
void basic_simplifier_plugin::set_eliminate_and(bool f) { m_rewriter->set_elim_and(f); }
void basic_simplifier_plugin::mk_iff(expr * lhs, expr * rhs, expr_ref & result) { mk_eq(lhs, rhs, result); }
void basic_simplifier_plugin::mk_xor(expr * lhs, expr * rhs, expr_ref & result) { m_rewriter->mk_xor(lhs, rhs, result); }
void basic_simplifier_plugin::mk_implies(expr * lhs, expr * rhs, expr_ref & result) { m_rewriter->mk_implies(lhs, rhs, result); }
void basic_simplifier_plugin::mk_ite(expr * c, expr * t, expr * e, expr_ref & result) { m_rewriter->mk_ite(c, t, e, result); }
void basic_simplifier_plugin::mk_and(unsigned num_args, expr * const * args, expr_ref & result) { m_rewriter->mk_and(num_args, args, result); }
void basic_simplifier_plugin::mk_or(unsigned num_args, expr * const * args, expr_ref & result) { m_rewriter->mk_or(num_args, args, result); }
void basic_simplifier_plugin::mk_and(expr * arg1, expr * arg2, expr_ref & result) { m_rewriter->mk_and(arg1, arg2, result); }
void basic_simplifier_plugin::mk_or(expr * arg1, expr * arg2, expr_ref & result) { m_rewriter->mk_or(arg1, arg2, result); }
void basic_simplifier_plugin::mk_and(expr * arg1, expr * arg2, expr * arg3, expr_ref & result) { m_rewriter->mk_and(arg1, arg2, arg3, result); }
void basic_simplifier_plugin::mk_or(expr * arg1, expr * arg2, expr * arg3, expr_ref & result) { m_rewriter->mk_or(arg1, arg2, arg3, result); }
void basic_simplifier_plugin::mk_nand(unsigned num_args, expr * const * args, expr_ref & result) { m_rewriter->mk_nand(num_args, args, result); } 
void basic_simplifier_plugin::mk_nor(unsigned num_args, expr * const * args, expr_ref & result) { m_rewriter->mk_nor(num_args, args, result); } 
void basic_simplifier_plugin::mk_nand(expr * arg1, expr * arg2, expr_ref & result) { m_rewriter->mk_nand(arg1, arg2, result); }
void basic_simplifier_plugin::mk_nor(expr * arg1, expr * arg2, expr_ref & result) { m_rewriter->mk_nor(arg1, arg2, result); }
void basic_simplifier_plugin::mk_distinct(unsigned num_args, expr * const * args, expr_ref & result) { m_rewriter->mk_distinct(num_args, args, result); }
void basic_simplifier_plugin::mk_not(expr * n, expr_ref & result) { m_rewriter->mk_not(n, result); }

void basic_simplifier_plugin::enable_ac_support(bool flag) {
    m_rewriter->set_flat(flag);
}
