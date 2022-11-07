/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat constraint manager

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#pragma once
#include "math/polysat/constraint.h"
#include "math/polysat/clause.h"
#include <iostream>

namespace polysat {

    class constraint;
    class ule_constraint;
    class umul_ovfl_constraint;
    class smul_fl_constraint;
    class op_constraint;
    class signed_constraint;

    using constraint_hash = obj_ptr_hash<constraint>;
    using constraint_eq = deref_eq<constraint>;
    using constraint_table = ptr_hashtable<constraint, constraint_hash, constraint_eq>;

    using constraints = ptr_vector<constraint>;
    using signed_constraints = vector<signed_constraint>;

    // Manage constraint lifetime, deduplication, and connection to boolean variables/literals.
    class constraint_manager {
        friend class constraint;

        solver& s;

        // Constraints indexed by their boolean variable
        ptr_vector<constraint> m_bv2constraint;
        // Constraints that have a boolean variable, for deduplication
        constraint_table m_constraint_table;
        scoped_ptr_vector<constraint> m_constraints;

        // scoped_ptr<constraint_dedup> m_dedup;

        // Clause storage per level
        vector<vector<clause_ref>> m_clauses;

        // Association to external dependency values (i.e., external names for constraints)
        u_map<constraint*> m_external_constraints;
        unsigned m_num_external = 0;

        // Manage association of constraints to boolean variables
        void assign_bv2c(sat::bool_var bv, constraint* c);
        void erase_bv2c(constraint* c);
        constraint* get_bv2c(sat::bool_var bv) const;

        void store(constraint* c);
        void erase(constraint* c);

        constraint* dedup(constraint* c);

        void gc_constraints(solver& s);
        void gc_clauses(solver& s);

        void watch(clause& cl, solver& s, bool value_propagate);
        void unwatch(clause& cl);

        void register_clause(clause* cl, solver& s);

        void ensure_bvar(constraint* c);
        void erase_bvar(constraint* c);

    public:
        constraint_manager(solver& s);
        ~constraint_manager();

        void store(clause* cl, solver& s, bool value_propagate);

        /// Release clauses at the given level and above.
        void release_level(unsigned lvl);

        /// Garbage-collect temporary constraints (i.e., those that do not have a boolean variable).
        void gc(solver& s);
        bool should_gc();

        constraint* lookup(sat::bool_var var) const;
        signed_constraint lookup(sat::literal lit) const;

        signed_constraint eq(pdd const& p);
        signed_constraint ule(pdd const& a, pdd const& b);
        signed_constraint ult(pdd const& a, pdd const& b);
        signed_constraint sle(pdd const& a, pdd const& b);
        signed_constraint slt(pdd const& a, pdd const& b);
        signed_constraint umul_ovfl(pdd const& p, pdd const& q);
        signed_constraint smul_ovfl(pdd const& p, pdd const& q);
        signed_constraint smul_udfl(pdd const& p, pdd const& q);
        signed_constraint bit(pdd const& p, unsigned i);
        signed_constraint lshr(pdd const& p, pdd const& q, pdd const& r);
        signed_constraint band(pdd const& p, pdd const& q, pdd const& r);

        pdd bnot(pdd const& p);
        pdd band(pdd const& p, pdd const& q);
        pdd bor(pdd const& p, pdd const& q);
        pdd bxor(pdd const& p, pdd const& q);
        pdd bnand(pdd const& p, pdd const& q);
        pdd bnor(pdd const& p, pdd const& q);

        constraint* const* begin() const { return m_constraints.data(); }
        constraint* const* end() const { return m_constraints.data() + m_constraints.size(); }

        using clause_iterator = decltype(m_clauses)::const_iterator;
        clause_iterator clauses_begin() const { return m_clauses.begin(); }
        clause_iterator clauses_end() const { return m_clauses.end(); }

        class clauses_t {
            constraint_manager const* m_cm;
        public:
            clauses_t(constraint_manager const& cm): m_cm(&cm) {}
            auto begin() const { return m_cm->clauses_begin(); }
            auto end() const { return m_cm->clauses_end(); }
        };
        clauses_t clauses() const { return {*this}; }
    };

}
