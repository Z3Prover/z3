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
#ifndef PULL_QUANT_H_
#define PULL_QUANT_H_

#include "ast/ast.h"

/**
   \brief Pull nested quantifiers in a formula. 
   
   \warning It assumes the input formula is in NNF.

   \remark pull_quant(F) is a quantifier if F contains a quantifier.
   
   \remark If pull_quant(F) is a quantifier then its weight is 
   Min{weight(Q') | Q' is a quantifier nested in F}
*/
class pull_quant {
    struct imp;
    imp *  m_imp;
public:
    pull_quant(ast_manager & m);
    ~pull_quant();
    void operator()(expr * n, expr_ref & r, proof_ref & p);
    void reset();
    void pull_quant2(expr * n, expr_ref & r, proof_ref & pr);
};

/**
   \brief After applying this transformation the formula will not
   contain nested quantifiers.
*/
class pull_nested_quant {
    struct imp;
    imp * m_imp;
public:
    pull_nested_quant(ast_manager & m);
    ~pull_nested_quant();
    void operator()(expr * n, expr_ref & r, proof_ref & p);
    void reset();
};

#endif /* PULL_QUANT_H_ */
