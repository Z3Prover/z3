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

        enum class kind_t {
            unassigned,
            bool_propagation,
            value_propagation,
            assumption,
            decision,
        };

        svector<sat::bool_var>  m_unused;   // previously deleted variables that can be reused by new_var();
        svector<lbool>          m_value;    // current value (indexed by literal)
        unsigned_vector         m_level;    // level of assignment (indexed by variable)
        dependency_vector       m_deps;     // dependencies of external asserts
        unsigned_vector         m_activity; //
        svector<kind_t>         m_kind;     // decision or propagation?
        // Clause associated with the assignment (indexed by variable):
        // - for propagations: the reason (or NULL for eval'd literals)
        // - for decisions: the lemma (or NULL for externally asserted literals)
        ptr_vector<clause>      m_clause;

        var_queue                   m_free_vars;  // free Boolean variables
        vector<ptr_vector<clause>>  m_watch;      // watch list for literals into clauses

        void assign(kind_t k, sat::literal lit, unsigned lvl, clause* reason, dependency dep = null_dependency);

    public:

        bool_var_manager(): m_free_vars(m_activity) {}

        // allocated size (not the number of active variables)
        unsigned size() const { return m_level.size(); }

        sat::bool_var new_var();
        void del_var(sat::bool_var var);

        bool is_assigned(sat::bool_var var) const { return value(var) != l_undef; }
        bool is_assigned(sat::literal lit) const { return value(lit) != l_undef; }
        bool is_decision(sat::bool_var var) const { return is_assigned(var) && m_kind[var] == kind_t::decision; }
        bool is_decision(sat::literal lit) const { return is_decision(lit.var()); }
        bool is_assumption(sat::bool_var var) const { return is_assigned(var) && m_kind[var] == kind_t::assumption; }
        bool is_assumption(sat::literal lit) const { return is_assumption(lit.var()); }
        bool is_bool_propagation(sat::bool_var var) const { return is_assigned(var) && m_kind[var] == kind_t::bool_propagation; }
        bool is_bool_propagation(sat::literal lit) const { return is_bool_propagation(lit.var()); }
        bool is_value_propagation(sat::bool_var var) const { return is_assigned(var) && m_kind[var] == kind_t::value_propagation; }
        bool is_value_propagation(sat::literal lit) const { return is_value_propagation(lit.var()); }
        lbool value(sat::bool_var var) const { return value(sat::literal(var)); }
        lbool value(sat::literal lit) const { return m_value[lit.index()]; }
        bool is_true(sat::literal lit) const { return value(lit) == l_true; }
        bool is_false(sat::literal lit) const { return value(lit) == l_false; }
        unsigned level(sat::bool_var var) const { SASSERT(is_assigned(var)); return m_level[var]; }
        unsigned level(sat::literal lit) const { return level(lit.var()); }
        clause* reason(sat::bool_var var) const { SASSERT(is_assigned(var)); return is_bool_propagation(var) ? m_clause[var] : nullptr; }
        clause* reason(sat::literal lit) const { return reason(lit.var()); }
        dependency dep(sat::literal lit) const { return lit == sat::null_literal ? null_dependency : m_deps[lit.var()]; }

        clause* lemma(sat::bool_var var) const { SASSERT(is_decision(var)); return m_clause[var]; }
       
        ptr_vector<clause>& watch(sat::literal lit) { return m_watch[lit.index()]; }
        unsigned_vector& activity() { return m_activity; }
        bool can_decide() const { return !m_free_vars.empty(); }
        sat::bool_var next_var() { return m_free_vars.next_var(); }
        void track_var(sat::literal lit) { m_free_vars.mk_var_eh(lit.var()); }

        // TODO connect activity updates with solver
        void inc_activity(sat::literal lit) { m_activity[lit.var()]++; }
        void dec_activity(sat::literal lit) { m_activity[lit.var()] /= 2; }

        /// Set the given literal to true
        void propagate(sat::literal lit, unsigned lvl, clause& reason);
        void decide(sat::literal lit, unsigned lvl, clause& lemma);
        void decide(sat::literal lit, unsigned lvl);
        void eval(sat::literal lit, unsigned lvl);
        void asserted(sat::literal lit, unsigned lvl, dependency dep);
        void unassign(sat::literal lit);

        std::ostream& display(std::ostream& out) const;

        friend std::ostream& operator<<(std::ostream& out, kind_t const& k) {
            switch (k) {
            case kind_t::unassigned: return out << "unassigned"; 
            case kind_t::bool_propagation: return out << "bool propagation"; 
            case kind_t::value_propagation: return out << "value propagation"; 
            case kind_t::decision: return out << "decision"; 
            default: UNREACHABLE(); return out;
            }
         }
    };

    inline std::ostream& operator<<(std::ostream& out, bool_var_manager const& m) { return m.display(out); }

}
