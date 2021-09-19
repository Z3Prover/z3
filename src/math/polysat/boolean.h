/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat boolean variables

Author:

    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/polysat/types.h"
#include "util/sat_literal.h"

namespace polysat {

    class clause;

    class bool_var_manager {
        svector<sat::bool_var>  m_unused;   // previously deleted variables that can be reused by new_var();
        svector<lbool>          m_value;    // current value (indexed by literal)
        svector<unsigned>       m_level;    // level of assignment (indexed by variable)
        unsigned_vector         m_activity; // 
        svector<clause*>        m_reason;   // propagation reason, NULL for decisions (indexed by variable)

        // For enumerative backtracking we store the lemma we're handling with a certain decision
        svector<clause*>        m_lemma;

        var_queue                   m_free_vars;  // free Boolean variables
        vector<ptr_vector<clause>>  m_watch;      // watch list for literals into clauses

    public:

        bool_var_manager(): m_free_vars(m_activity) {}

        // allocated size (not the number of active variables)
        unsigned size() const { return m_level.size(); }

        sat::bool_var new_var();
        void del_var(sat::bool_var var);

        bool is_assigned(sat::bool_var var) const { return value(var) != l_undef; }
        bool is_assigned(sat::literal lit) const { return value(lit) != l_undef; }
        bool is_decision(sat::bool_var var) const { return is_assigned(var) && !reason(var); }
        bool is_decision(sat::literal lit) const { return is_decision(lit.var()); }
        bool is_propagation(sat::bool_var var) const { return is_assigned(var) && reason(var); }
        lbool value(sat::bool_var var) const { return value(sat::literal(var)); }
        lbool value(sat::literal lit) const { return m_value[lit.index()]; }
        bool is_true(sat::literal lit) const { return value(lit) == l_true; }
        bool is_false(sat::literal lit) const { return value(lit) == l_false; }
        unsigned level(sat::bool_var var) const { SASSERT(is_assigned(var)); return m_level[var]; }
        unsigned level(sat::literal lit) const { return level(lit.var()); }
        clause* reason(sat::bool_var var) const { SASSERT(is_assigned(var)); return m_reason[var]; }

        clause* lemma(sat::bool_var var) const { SASSERT(is_decision(var)); return m_lemma[var]; }

        

        ptr_vector<clause>& watch(sat::literal lit) { return m_watch[lit.index()]; }
        unsigned_vector& activity() { return m_activity; }
        bool can_decide() const { return !m_free_vars.empty(); }
        sat::bool_var next_var() { return m_free_vars.next_var(); }

        // TODO connect activity updates with solver
        void inc_activity(sat::literal lit) { m_activity[lit.var()]++; }
        void dec_activity(sat::literal lit) { m_activity[lit.var()] /= 2; }

        /// Set the given literal to true
        void assign(sat::literal lit, unsigned lvl, clause* reason, clause* lemma);
        void unassign(sat::literal lit);

        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, bool_var_manager const& m) { return m.display(out); }

}
