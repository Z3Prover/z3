/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    euclidean_solver.h

Abstract:

    Euclidean Solver with support for explanations.

Author:

    Leonardo de Moura (leonardo) 2011-07-08.

Revision History:

--*/
#ifndef EUCLIDEAN_SOLVER_H_
#define EUCLIDEAN_SOLVER_H_

#include"mpq.h"
#include"vector.h"

class euclidean_solver {
    struct imp;
    imp *  m_imp;
public:
    typedef unsigned               var;
    typedef unsigned               justification;
    typedef unsynch_mpq_manager    numeral_manager;
    typedef svector<justification> justification_vector;
    static const justification     null_justification = UINT_MAX;
    
    /**
       \brief If m == 0, then the solver will create its own numeral manager.
    */
    euclidean_solver(numeral_manager * m);
    
    ~euclidean_solver();
    
    numeral_manager & m() const;
    
    /**
       \brief Reset the state of the euclidean solver.
    */
    void reset();
    
    /**
       \brief Creates a integer variable.
    */
    var mk_var();
    
    /**
       \brief Creates a fresh justification id.
    */
    justification mk_justification();

    /**
       \brief Asserts an equation of the form as[0]*xs[0] + ... + as[num-1]*xs[num-1] + c = 0 with justification j.

       The numerals must be created using the numeral_manager m().
    */
    void assert_eq(unsigned num, mpz const * as, var const * xs, mpz const & c, justification j = null_justification);
    
    /**
       \brief Solve the current set of equations. Return false if it is inconsistent.
    */
    bool solve();

    /**
       \brief Return a set of justifications (proof) for the inconsitency.

       \pre inconsistent()
    */
    justification_vector const & get_justification() const;
    
    bool inconsistent() const;

    /**
       \brief Return true if the variable is a "parameter" created by the Euclidean solver.
    */
    bool is_parameter(var x) const;
    
    /**
       Given a linear polynomial as[0]*xs[0] + ... + as[num-1]*xs[num-1] + c and the current solution set,
       It applies the solution set to produce a polynomial of the for a_prime * p + c_prime, where
       a_prime * p represents a linear polynomial where the coefficient of every monomial is a multiple of
       a_prime.
       
       The justification is stored in js.
       Note that, this function does not return the actual p.

       The numerals must be created using the numeral_manager m().
    */
    void normalize(unsigned num, mpz const * as, var const * xs, mpz const & c, mpz & a_prime, mpz & c_prime, justification_vector & js);

    /**
       \brief Set/Reset the cancel flag.
    */
    void set_cancel(bool f);

    void display(std::ostream & out) const;
};

#endif
