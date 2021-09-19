/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat constraints

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/polysat/boolean.h"
#include "math/polysat/clause.h"
#include "math/polysat/types.h"
#include "math/polysat/interval.h"

namespace polysat {

    enum ckind_t { ule_t };

    class constraint;
    class ule_constraint;
    class signed_constraint;

    using constraint_hash = obj_ptr_hash<constraint>;
    using constraint_eq = deref_eq<constraint>;
    using constraint_table = ptr_hashtable<constraint, constraint_hash, constraint_eq>;

    using constraints = ptr_vector<constraint>;
    using signed_constraints = vector<signed_constraint>;

    // Manage constraint lifetime, deduplication, and connection to boolean variables/literals.
    class constraint_manager {
        friend class constraint;

        bool_var_manager& m_bvars;

        // Constraints indexed by their boolean variable
        ptr_vector<constraint> m_bv2constraint;
        // Constraints that have a boolean variable, for deduplication
        constraint_table m_constraint_table;
        scoped_ptr_vector<constraint> m_constraints;

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

        void watch(clause& cl, solver& s);
        void unwatch(clause& cl);

    public:
        constraint_manager(bool_var_manager& bvars): m_bvars(bvars) {}
        ~constraint_manager();

        void ensure_bvar(constraint* c);
        void erase_bvar(constraint* c);
        // sat::literal get_or_assign_blit(signed_constraint& c);

        void store(clause* cl, solver& s);

        /// Register a unit clause with an external dependency.
        void register_external(signed_constraint c);
        void unregister_external(constraint* c);
        signed_constraint lookup_external(unsigned dep) const;

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

        constraint *const* begin() const { return m_constraints.data(); }
        constraint *const* end() const { return m_constraints.data() + m_constraints.size(); }

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


    /// Normalized inequality:
    ///     lhs <= rhs, if !is_strict
    ///     lhs < rhs, otherwise
    struct inequality {
        pdd lhs;
        pdd rhs;
        bool is_strict;
        constraint const* src;  // TODO: should be signed_constraint now
        inequality(pdd const & lhs, pdd const & rhs, bool is_strict, constraint const* src):
            lhs(lhs), rhs(rhs), is_strict(is_strict), src(src) {}
        signed_constraint as_signed_constraint() const;
    };


    class constraint {
        friend class constraint_manager;
        friend class clause;
        friend class ule_constraint;

        // constraint_manager* m_manager;
        clause*             m_unit_clause = nullptr;  ///< If this constraint was asserted by a unit clause, we store that clause here.
        ckind_t             m_kind;
        unsigned_vector     m_vars;
        lbool               m_external_sign = l_undef;
        bool                m_is_marked = false;
        bool                m_is_var_dependent = false;
        /** The boolean variable associated to this constraint, if any.
         *  If this is not null_bool_var, then the constraint corresponds to a literal on the assignment stack.
         *  Convention: the plain constraint corresponds the positive sat::literal.
         */
        sat::bool_var       m_bvar = sat::null_bool_var;

        constraint(constraint_manager& m, ckind_t k): m_kind(k) {}
        

    public:
        virtual ~constraint() {}

        virtual unsigned hash() const = 0;
        virtual bool operator==(constraint const& other) const = 0;
        bool operator!=(constraint const& other) const { return !operator==(other); }

        virtual bool is_eq() const { return false; }
        bool is_ule() const { return m_kind == ckind_t::ule_t; }
        ckind_t kind() const { return m_kind; }
        virtual std::ostream& display(std::ostream& out, lbool status) const = 0;
        virtual std::ostream& display(std::ostream& out) const = 0;

        bool propagate(solver& s, bool is_positive, pvar v);
        virtual void propagate_core(solver& s, bool is_positive, pvar v, pvar other_v);
        virtual bool is_always_false(bool is_positive) const = 0;
        virtual bool is_currently_false(solver& s, bool is_positive) const = 0;
        virtual bool is_currently_true(solver& s, bool is_positive) const = 0;
        virtual void narrow(solver& s, bool is_positive) = 0;
        virtual inequality as_inequality(bool is_positive) const = 0;

        ule_constraint& to_ule();
        ule_constraint const& to_ule() const;
        unsigned_vector& vars() { return m_vars; }
        unsigned_vector const& vars() const { return m_vars; }
        unsigned var(unsigned idx) const { return m_vars[idx]; }
        bool contains_var(pvar v) const { return m_vars.contains(v); }
        bool has_bvar() const { return m_bvar != sat::null_bool_var; }
        sat::bool_var bvar() const { return m_bvar; }
        std::string bvar2string() const;
        unsigned level(solver& s) const;

        clause* unit_clause() const { return m_unit_clause; }
        void set_unit_clause(clause* cl);
        p_dependency* unit_dep() const { return m_unit_clause ? m_unit_clause->dep() : nullptr; }

        void set_external(bool sign) { m_external_sign = to_lbool(sign); }
        void unset_external() { m_external_sign = l_undef; }
        bool is_external() const { return m_external_sign != l_undef; }
        bool external_sign() const { SASSERT(is_external()); return m_external_sign == l_true; }

        void set_mark() { m_is_marked = true; }
        void unset_mark() { m_is_marked = false; }
        bool is_marked() const { return m_is_marked; }

        void set_var_dependent() { m_is_var_dependent = true; }
        void unset_var_dependent() { m_is_var_dependent = false; }
        bool is_var_dependent() { return m_is_var_dependent;  }
    };

    inline std::ostream& operator<<(std::ostream& out, constraint const& c) { return c.display(out); }


    class signed_constraint final {
    public:
        using ptr_t = constraint*;

    private:
        ptr_t m_constraint = nullptr;
        bool m_positive = true;

    public:
        signed_constraint() {}
        signed_constraint(constraint* c, bool is_positive):
            m_constraint(c), m_positive(is_positive) {}
        signed_constraint(constraint* c, sat::literal lit):
            signed_constraint(c, !lit.sign()) {
            SASSERT_EQ(blit(), lit);
        }

        void negate() { m_positive = !m_positive; }
        signed_constraint operator~() const { return {get(), !is_positive()}; }

        bool is_positive() const { return m_positive; }
        bool is_negative() const { return !is_positive(); }

        bool propagate(solver& s, pvar v) { return get()->propagate(s, is_positive(), v); }
        void propagate_core(solver& s, pvar v, pvar other_v) { get()->propagate_core(s, is_positive(), v, other_v); }
        bool is_always_false() const { return get()->is_always_false(is_positive()); }
        bool is_always_true() const { return get()->is_always_false(is_negative()); }
        bool is_currently_false(solver& s) const { return get()->is_currently_false(s, is_positive()); }
        bool is_currently_true(solver& s) const { return get()->is_currently_true(s, is_positive()); }
        lbool bvalue(solver& s) const;
        unsigned level(solver& s) const { return get()->level(s); }
        void narrow(solver& s) { get()->narrow(s, is_positive()); }
        inequality as_inequality() const { return get()->as_inequality(is_positive()); }

        sat::bool_var bvar() const { return m_constraint->bvar(); }
        sat::literal blit() const { return sat::literal(bvar(), is_negative()); }
        constraint* get() const { return m_constraint; }
        

        explicit operator bool() const { return !!m_constraint; }
        bool operator!() const { return !m_constraint; }
        constraint* operator->() const { return get(); }
        constraint& operator*() { return *m_constraint; }
        constraint const& operator*() const { return *m_constraint; }


        signed_constraint& operator=(std::nullptr_t) { m_constraint = nullptr; return *this; }

        unsigned hash() const {
            return combine_hash(get_ptr_hash(get()), bool_hash()(is_positive()));
        }
        bool operator==(signed_constraint const& other) const {
            return get() == other.get() && is_positive() == other.is_positive();
        }
        bool operator!=(signed_constraint const& other) const { return !operator==(other); }

        std::ostream& display(std::ostream& out) const {
            if (m_constraint)
                return m_constraint->display(out, to_lbool(is_positive()));
            else
                return out << "<null>";
        }
    };

    inline std::ostream& operator<<(std::ostream& out, signed_constraint const& c) {
        return c.display(out);
    }
}
