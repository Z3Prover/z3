/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat boolean variables

Author:

    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/polysat/types.h"

namespace polysat {

    class bool_var_manager {

        enum class kind_t {
            unassigned,
            decision,
            /// input constraint
            assumption,
            /// propagated due to boolean clause
            bool_propagation,
            /// evaluated under pvar assignment
            evaluation,
        };

        svector<sat::bool_var>      m_unused;   // previously deleted variables that can be reused by new_var();
        svector<lbool>              m_value;    // current value (indexed by literal)
        unsigned_vector             m_level;    // level of assignment (indexed by variable)
        dependency_vector           m_deps;     // dependencies of external asserts
        svector<kind_t>             m_kind;     // decision or propagation?
        ptr_vector<clause>          m_reason;   // reasons for bool-propagated literals
        vector<ptr_vector<clause>>  m_watch;    // watch list for literals into clauses

        void assign(kind_t k, sat::literal lit, unsigned lvl, clause* reason, dependency dep = null_dependency);
        bool invariant(sat::bool_var var) const;
        bool invariant(sat::literal lit) const { return invariant(lit.var()); }

    public:
        bool_var_manager() {}

        // allocated size (not the number of active variables)
        unsigned size() const { return m_level.size(); }

        sat::bool_var new_var();
        void del_var(sat::bool_var var);

        bool is_assigned(sat::bool_var var) const { SASSERT(invariant(var)); return value(var) != l_undef; }
        bool is_assigned(sat::literal lit) const { SASSERT(invariant(lit)); return value(lit) != l_undef; }
        bool is_assumption(sat::bool_var var) const { SASSERT(invariant(var)); return m_kind[var] == kind_t::assumption; }
        bool is_assumption(sat::literal lit) const { return is_assumption(lit.var()); }
        bool is_decision(sat::bool_var var) const { SASSERT(invariant(var)); return m_kind[var] == kind_t::decision; }
        bool is_decision(sat::literal lit) const { return is_decision(lit.var()); }
        bool is_bool_propagation(sat::bool_var var) const { SASSERT(invariant(var)); return m_kind[var] == kind_t::bool_propagation; }
        bool is_bool_propagation(sat::literal lit) const { return is_bool_propagation(lit.var()); }
        bool is_evaluation(sat::bool_var var) const { SASSERT(invariant(var)); return m_kind[var] == kind_t::evaluation; }
        bool is_evaluation(sat::literal lit) const { return is_evaluation(lit.var()); }
        lbool value(sat::bool_var var) const { return value(sat::literal(var)); }
        lbool value(sat::literal lit) const { return m_value[lit.index()]; }
        bool is_true(sat::literal lit) const { return value(lit) == l_true; }
        bool is_false(sat::literal lit) const { return value(lit) == l_false; }
        unsigned level(sat::bool_var var) const { SASSERT(is_assigned(var)); return m_level[var]; }
        unsigned level(sat::literal lit) const { return level(lit.var()); }
        clause* reason(sat::bool_var var) const { SASSERT(is_assigned(var)); SASSERT(is_bool_propagation(var) == !!m_reason[var]); return m_reason[var]; }
        clause* reason(sat::literal lit) const { return reason(lit.var()); }
        dependency dep(sat::literal lit) const { return lit == sat::null_literal ? null_dependency : m_deps[lit.var()]; }

        ptr_vector<clause>& watch(sat::literal lit) { return m_watch[lit.index()]; }

        /// Set the given literal to true
        void propagate(sat::literal lit, unsigned lvl, clause& reason);
        void eval(sat::literal lit, unsigned lvl);
        void assumption(sat::literal lit, unsigned lvl, dependency dep);
        void decision(sat::literal lit, unsigned lvl);

        void unassign(sat::literal lit);

        std::ostream& display(std::ostream& out) const;
        std::ostream& display_justification(sat::literal lit, std::ostream& out) const;

        friend std::ostream& operator<<(std::ostream& out, kind_t const& k) {
            switch (k) {
            case kind_t::unassigned: return out << "unassigned";
            case kind_t::bool_propagation: return out << "bool propagation";
            case kind_t::evaluation: return out << "evaluation";
            case kind_t::assumption: return out << "assumption";
            case kind_t::decision: return out << "decision";
            }
            UNREACHABLE();
            return out;
        }
    };

    struct bool_justification_pp {
        bool_var_manager const& b;
        sat::literal lit;
        bool_justification_pp(bool_var_manager const& b, sat::literal lit) : b(b), lit(lit) {}
    };

    inline std::ostream& operator<<(std::ostream& out, bool_var_manager const& m) { return m.display(out); }

    inline std::ostream& operator<<(std::ostream& out, bool_justification_pp const& p) { return p.b.display_justification(p.lit, out); }

}
