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
#ifndef NLSAT_EXPLAIN_H_
#define NLSAT_EXPLAIN_H_

#include"nlsat_solver.h"
#include"nlsat_scoped_literal_vector.h"
#include"polynomial_cache.h"

namespace nlsat {
    class evaluator;
    
    class explain {
    public:
        struct imp;
    private:
        imp * m_imp;
    public:
        explain(solver & s, assignment const & x2v, polynomial::cache & u, atom_vector const & atoms, atom_vector const & x2eq,
                evaluator & ev);
        ~explain();

        void reset();
        void set_simplify_cores(bool f);
        void set_full_dimensional(bool f);
        void set_minimize_cores(bool f);
        void set_factor(bool f);

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
    };

};

#endif
