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
        class compare_occ;

        simplifier& simp;
        solver&     s;
        bdd_manager m;
        random_gen  m_rand;


        svector<bool_var> m_vars;
        unsigned_vector   m_mark;
        unsigned          m_mark_lim;
        unsigned_vector   m_var2index;
        unsigned_vector   m_occ;
        unsigned          m_miss;
        unsigned          m_hit1;
        unsigned          m_hit2;

        unsigned m_max_literals;

        unsigned num_vars() const { return m_vars.size(); }
        void reset_mark();
        void mark_var(bool_var v);
        void sort_marked();
        void shuffle_vars();
        bool mark_literals(clause_use_list & occs);
        bool mark_literals(literal lit);
        bdd make_clauses(clause_use_list & occs);
        bdd make_clauses(literal lit);
        bdd mk_literal(literal l);
        void get_clauses(bdd const& b, literal_vector& lits, clause_vector& clauses, literal_vector& units);
        void add_clauses(bool_var v, bdd const& b, literal_vector& lits);
        bool elim_var(bool_var v, bdd const& b);
        bdd  elim_var(bool_var v);

    public:
        elim_vars(simplifier& s);
        bool operator()(bool_var v);
        unsigned hit2() const { return m_hit1; } // first round bdd construction is minimal
        unsigned hit1() const { return m_hit2; } // minimal after reshufling
        unsigned miss() const { return m_miss; } // not-minimal
    };

};

#endif
