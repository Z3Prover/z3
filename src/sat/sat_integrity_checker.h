/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_integrity_checker.h

Abstract:

    Checker whether the SAT solver internal datastructures 
    are consistent or not.

Author:

    Leonardo de Moura (leonardo) 2011-05-21.

Revision History:

--*/
#ifndef SAT_INTEGRITY_CHECKER_H_
#define SAT_INTEGRITY_CHECKER_H_

#include"sat_types.h"

namespace sat {
    class integrity_checker {
        solver const & s;
    public:
        integrity_checker(solver const & s);
        
        bool check_clause(clause const & c) const;
        bool check_clauses(clause * const * begin, clause * const * end) const;
        bool check_clauses() const;
        bool check_learned_clauses() const;
        bool check_assignment() const;
        bool check_bool_vars() const;
        bool check_watches() const;
        bool check_reinit_stack() const;
        bool check_disjoint_clauses() const;
        bool operator()() const;
    };
};
#endif
