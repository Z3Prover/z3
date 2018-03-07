/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    expr2polynomial.h

Abstract:

    Translator from Z3 expressions into multivariate polynomials (and back).
    
    
Author:

    Leonardo (leonardo) 2011-12-23

Notes:

--*/
#ifndef EXPR2POLYNOMIAL_H_
#define EXPR2POLYNOMIAL_H_

#include "ast/ast.h"
#include "math/polynomial/polynomial.h"

class expr2var;

class expr2polynomial {
    struct imp;
    imp * m_imp;
public:
    expr2polynomial(ast_manager & am, 
                    polynomial::manager & pm, 
                    expr2var * e2v,
                    /*
                      If true, the expressions converted into 
                      polynomials should only contain Z3 free variables.
                      A Z3 variable x, with idx i, is converted into
                      the variable i of the polynomial manager pm.
                      
                      An exception is thrown if there is a mismatch between
                      the sorts x and the variable in the polynomial manager.

                      The argument e2v is ignored when use_var_idxs is true.

                      Moreover, only real variables are allowed.
                    */
                    bool use_var_idxs = false
                    );
    virtual ~expr2polynomial();

    ast_manager & m() const;
    polynomial::manager & pm() const;
    
    /**
       \brief Convert a Z3 expression into a polynomial in Z[x0, ..., x_n].
       Since Z3 expressions may be representing polynomials in Q[x0, ..., x_n],
       the method also returns a "denominator" d. 
       Thus, we have that n is equal to p/d

       \remark Return false if t is not an integer or real expression.
       
       \pre The only supported operators are MUL, ADD, SUB, UMINUS, TO_REAL, TO_INT, POWER (with constants) 
    */
    bool to_polynomial(expr * t, polynomial::polynomial_ref & p, polynomial::scoped_numeral & d);
    
    /**
       \brief Convert a polynomial into a Z3 expression.
       
       \remark If the polynomial has one real variable, then the resultant 
       expression is an real expression. Otherwise, it is an integer
    */
    void to_expr(polynomial::polynomial_ref const & p, bool use_power, expr_ref & r);

    /**
       \brief Return true if t was encoded as a variable by the translator.
    */
    bool is_var(expr * t) const;
    
    
    /**
       \brief Return the mapping from expressions to variables
    
       \pre the object was created using use_var_idxs = false.
    */
    expr2var const & get_mapping() const;

    /**
       \brief Cancel/Interrupt execution.
    */
    void set_cancel(bool f);

    /**
       \brief Return true if the variable is associated with an expression of integer sort.
    */
    virtual bool is_int(polynomial::var x) const { UNREACHABLE(); return false; }

protected:
    virtual polynomial::var mk_var(bool is_int) { UNREACHABLE(); return polynomial::null_var; }
};

class default_expr2polynomial : public expr2polynomial {
    svector<bool> m_is_int;
public:
    default_expr2polynomial(ast_manager & am, polynomial::manager & pm);
    ~default_expr2polynomial() override;
    bool is_int(polynomial::var x) const override;
protected:
    polynomial::var mk_var(bool is_int) override;
};

#endif
