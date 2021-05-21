/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat boolean variables

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/polysat/types.h"
#include "util/sat_literal.h"

namespace polysat {

    class clause;

    class bool_var_manager {
        svector<sat::bool_var>  m_unused;  // previously deleted variables that can be reused by new_var();
        svector<lbool>          m_value;   // current value (indexed by literal)
        svector<unsigned>       m_level;   // level of assignment (indexed by variable)
        svector<clause*>        m_reason;  // propagation reason, NULL for decisions (indexed by variable)

        // For enumerative backtracking we store the lemma we're handling with a certain decision
        svector<clause*>        m_lemma;

        unsigned_vector         m_marks;
        unsigned                m_clock { 0 };

        // allocated size (not the number of active variables)
        unsigned size() const { return m_level.size(); }

    public:
        sat::bool_var new_var();
        void del_var(sat::bool_var var);

        void reset_marks();
        bool is_marked(sat::bool_var var) const { return m_clock == m_marks[var]; }
        void set_mark(sat::bool_var var);

        bool is_assigned(sat::bool_var var) const { return value(var) != l_undef; }
        bool is_assigned(sat::literal lit) const { return value(lit) != l_undef; }
        bool is_decision(sat::bool_var var) const { return is_assigned(var) && !reason(var); }
        // bool is_decision(bool_lit lit) const { return is_decision(lit.var()); }
        bool is_propagation(sat::bool_var var) const { return is_assigned(var) && reason(var); }
        lbool value(sat::bool_var var) const { return value(sat::literal(var)); }
        lbool value(sat::literal lit) const { return m_value[lit.index()]; }
        unsigned level(sat::bool_var var) const { SASSERT(is_assigned(var)); return m_level[var]; }
        // unsigned level(sat::literal lit) const { return level(lit.var()); }
        clause* reason(sat::bool_var var) const { SASSERT(is_assigned(var)); return m_reason[var]; }

        clause* lemma(sat::bool_var var) const { SASSERT(is_decision(var)); return m_lemma[var]; }

        /// Set the given literal to true
        void assign(sat::literal lit, unsigned lvl, clause* reason, clause* lemma);
        void unassign(sat::literal lit);
    };

}
