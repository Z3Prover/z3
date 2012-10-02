/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    pull_quant.h

Abstract:

    Pull nested quantifiers.

Author:

    Leonardo (leonardo) 2008-01-20

Notes:

--*/
#ifndef _PULL_QUANT_H_
#define _PULL_QUANT_H_

#include"simplifier.h"
#include"var_subst.h"

/**
   \brief Pull nested quantifiers in a formula. 
   
   \warning It assumes the input formula is in NNF.

   \remark pull_quant(F) is a quantifier if F contains a quantifier.
   
   \remark If pull_quant(F) is a quantifier then its weight is 
   Min{weight(Q') | Q' is a quantifier nested in F}
*/
class pull_quant : public base_simplifier {
protected:    
    shift_vars m_shift;
    bool visit_children(expr * n);
    void reduce1(expr *);
    void reduce1_app(app * n);
    void reduce1_quantifier(quantifier * q);
    
public:
    pull_quant(ast_manager & m);
    virtual ~pull_quant() {}
    void operator()(expr * n, expr_ref & r, proof_ref & p);
    void reset() { flush_cache(); }
    void pull_quant1(func_decl * d, unsigned num_children, expr * const * children, expr_ref & result);
    void pull_quant1(quantifier * q, expr * new_expr, expr_ref & result);
    void pull_quant1(expr * n, expr_ref & result);
    void pull_quant2(expr * n, expr_ref & r, proof_ref & pr);
};

/**
   \brief After applying this transformation the formula will not
   contain nested quantifiers.
*/
class pull_nested_quant : public simplifier {
    pull_quant   m_pull;
    virtual bool visit_quantifier(quantifier * q);
    virtual void reduce1_quantifier(quantifier * q);
public:
    pull_nested_quant(ast_manager & m):simplifier(m), m_pull(m) { enable_ac_support(false); }
    virtual ~pull_nested_quant() {}
};

#endif /* _PULL_QUANT_H_ */
