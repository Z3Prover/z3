/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    expr2subpaving.h

Abstract:

    Translator from Z3 expressions into generic subpaving data-structure.
    
    
Author:

    Leonardo (leonardo) 2012-08-08

Notes:

--*/
#ifndef _EXPR2SUBPAVING_H_
#define _EXPR2SUBPAVING_H_

#include"ast.h"
#include"subpaving.h"

class expr2var;

class expr2subpaving {
    struct imp;
    imp *  m_imp;
public:
    expr2subpaving(ast_manager & m, subpaving::context & s, expr2var * e2v = 0);
    ~expr2subpaving();

    ast_manager & m() const;

    subpaving::context & s() const;
    
    /**
       \brief Return true if t was encoded as a variable by the translator.
    */
    bool is_var(expr * t) const;
    
    /**
       \brief Cancel/Interrupt execution.
    */
    void set_cancel(bool f);
    
    /**
       \brief Internalize a Z3 arithmetical expression into the subpaving data-structure.

       \remark throws subpaving::exception there is a translation error (when using imprecise representations, i.e. floats, in the subpaving module)
    */
    subpaving::var internalize_term(expr * t, /* out */ mpz & n, /* out */ mpz & d);
};


#endif
