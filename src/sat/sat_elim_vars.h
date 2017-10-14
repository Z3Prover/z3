/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    sat_elim_vars.h

Abstract:

    Helper class for eliminating variables

Author:

    Nikolaj Bjorner (nbjorner) 2017-10-14

Revision History:

--*/
#ifndef SAT_ELIM_VARS_H_
#define SAT_ELIM_VARS_H_

#include "sat/sat_types.h"
#include "sat/sat_bdd.h"

namespace sat {
    class solver;
    class simplifier;

    class elim_vars {
        friend class simplifier;

        simplifier& simp;
        solver&     s;
        bdd_manager m;

        svector<bool_var> m_vars;
        unsigned_vector   m_mark;
        unsigned          m_mark_lim;
        unsigned_vector   m_var2index;

        unsigned m_max_literals;

        unsigned num_vars() const { return m_vars.size(); }
        void reset_mark();
        void mark_var(bool_var v);
        bool mark_literals(clause_use_list & occs);
        bool mark_literals(literal lit);
        bdd make_clauses(clause_use_list & occs);
        bdd make_clauses(literal lit);
        bdd mk_literal(literal l);
        void get_clauses(bdd const& b, literal_vector& lits, clause_vector& clauses, literal_vector& units);
        void add_clauses(bdd const& b, literal_vector& lits);

    public:
        elim_vars(simplifier& s);
        bool operator()(bool_var v);
    };

};

#endif
