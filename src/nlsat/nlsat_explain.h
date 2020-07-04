/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_explain.h

Abstract:

    Functor that implements the "explain" procedure defined in Dejan and Leo's paper.

Author:

    Leonardo de Moura (leonardo) 2012-01-13.

Revision History:

--*/
#pragma once

#include "nlsat/nlsat_solver.h"
#include "nlsat/nlsat_scoped_literal_vector.h"
#include "math/polynomial/polynomial_cache.h"
#include "math/polynomial/algebraic_numbers.h"

namespace nlsat {
    class evaluator;

    
    class explain {
    public:
        struct imp;
    private:
        imp * m_imp;
    public:
        explain(solver & s, assignment const & x2v, polynomial::cache & u, 
                atom_vector const& atoms, atom_vector const& x2eq, evaluator & ev);
        ~explain();

        void reset();
        void set_simplify_cores(bool f);
        void set_full_dimensional(bool f);
        void set_minimize_cores(bool f);
        void set_factor(bool f);
        void set_signed_project(bool f);

        /**
           \brief Given a set of literals ls[0], ... ls[n-1] s.t.
           - n > 0
           - all of them are arithmetic literals.
           - all of them have the same maximal variable.
           - (ls[0] and ... and ls[n-1]) is infeasible in the current interpretation.

           Let x be the maximal variable in {ls[0], ..., ls[n-1]}.

           Remark: the current interpretation assigns all variables in ls[0], ..., ls[n-1] but x.

           This procedure stores in result a set of literals: s_1, ..., s_m
           s.t.
                 - (s_1 or ... or s_m or ~ls[0] or ... or ~ls[n-1]) is a valid clause
                 - s_1, ..., s_m do not contain variable x.
                 - s_1, ..., s_m are false in the current interpretation
        */
        void operator()(unsigned n, literal const * ls, scoped_literal_vector & result);

        
        /**
           \brief projection for a given variable.

             Given:    M |= l1[x] /\ ... /\ ln[x]
           
             Find:     M |= s1, ..., sm

             Such that:  |= ~s1 \/ ... \/ ~sm \/ E x. l1[x] /\ ... /\ ln[x]

           Contrast this with with the core-based projection above:

             Given:     M |= A x . l1[x] \/  ... \/ ln[x]
           
             Find:      M |= ~s1, ..., ~sm.

             Such that:   |= s1 \/ ... \/ sm \/ A x . l1[x] \/  ... \/ ln[x]           

           Claim: the two compute the same solutions if the projection operators are independent of the value of x.
           Claim: A complete, convergent projection operator can be obtained from M in a way that is independent of x.

           
         */
        void project(var x, unsigned n, literal const * ls, scoped_literal_vector & result);

        /**
           Maximize the value of x (locally) under the current assignment to other variables and
           while maintaining the assignment to the literals ls.
           Set unbounded to 'true' if the value of x is unbounded.

           Precondition: the set of literals are true in the current model.

           By local optimization we understand that x is increased to the largest value within
           the signs delineated by the roots of the polynomials in ls.
         */
        void maximize(var x, unsigned n, literal const * ls, scoped_anum& val, bool& unbounded);

        /**
           Unit test routine.
         */
        void test_root_literal(atom::kind k, var y, unsigned i, poly* p, scoped_literal_vector & result);
    };

};

