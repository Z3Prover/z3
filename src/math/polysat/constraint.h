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

    enum ckind_t { eq_t, ule_t };

    class constraint;
    class eq_constraint;
    class ule_constraint;
    class signed_constraint;

    using constraint_table = ptr_hashtable<constraint, obj_ptr_hash<constraint>, deref_eq<constraint>>;

    // Manage constraint lifetime, deduplication, and connection to boolean variables/literals.
    class constraint_manager {
        friend class constraint;

        bool_var_manager& m_bvars;

        // Constraints indexed by their boolean variable
        ptr_vector<constraint> m_bv2constraint;
        // Constraints that have a boolean variable, for deduplication
        constraint_table m_constraint_table;

        // Constraint storage per level

        vector<scoped_ptr_vector<constraint>> m_constraints;
        vector<vector<clause_ref>> m_clauses;

        // Association to external dependency values (i.e., external names for constraints)
        u_map<constraint*> m_external_constraints;

        // Manage association of constraints to boolean variables
        void assign_bv2c(sat::bool_var bv, constraint* c);
        void erase_bv2c(constraint* c);
        constraint* get_bv2c(sat::bool_var bv) const;

        void store(constraint* c);
        void erase(constraint* c);
        void set_level(constraint* c, unsigned new_lvl);

        constraint* dedup(constraint* c);

    public:
        constraint_manager(bool_var_manager& bvars): m_bvars(bvars) {}
        ~constraint_manager();

        void ensure_bvar(constraint* c);
        void erase_bvar(constraint* c);
        // sat::literal get_or_assign_blit(signed_constraint& c);

        clause* store(clause_ref cl);

        /// Register a unit clause with an external dependency.
        void register_external(constraint* c);

        /// Release constraints at the given level and above.
        void release_level(unsigned lvl);

        /// Garbage-collect temporary constraints (i.e., those that do not have a boolean variable).
        void gc();
        bool should_gc();

        constraint* lookup(sat::bool_var var) const;
        signed_constraint lookup(sat::literal lit) const;
        constraint* lookup_external(unsigned dep) const { return m_external_constraints.get(dep, nullptr); }

        signed_constraint eq(unsigned lvl, pdd const& p);
        signed_constraint ule(unsigned lvl, pdd const& a, pdd const& b);
        signed_constraint ult(unsigned lvl, pdd const& a, pdd const& b);
        signed_constraint sle(unsigned lvl, pdd const& a, pdd const& b);
        signed_constraint slt(unsigned lvl, pdd const& a, pdd const& b);
    };


    /// Normalized inequality:
    ///     lhs <= rhs, if !is_strict
    ///     lhs < rhs, otherwise
    struct inequality {
        pdd lhs;
        pdd rhs;
        bool is_strict;
        constraint const* src;
        inequality(pdd const & lhs, pdd const & rhs, bool is_strict, constraint const* src):
            lhs(lhs), rhs(rhs), is_strict(is_strict), src(src) {}
    };


    class constraint {
        friend class constraint_manager;
        friend class clause;
        friend class eq_constraint;
        friend class ule_constraint;

        // constraint_manager* m_manager;
        clause*             m_unit_clause = nullptr;  ///< If this constraint was asserted by a unit clause, we store that clause here.
        unsigned            m_level;  ///< Controls lifetime of the constraint object. Always a base level.
        ckind_t             m_kind;
        unsigned_vector     m_vars;
        /** The boolean variable associated to this constraint, if any.
         *  If this is not null_bool_var, then the constraint corresponds to a literal on the assignment stack.
         *  Convention: the plain constraint corresponds the positive sat::literal.
         */
        // NB code review: the convention would make sense. Unfortunately, elsewhere in z3 we use "true" for negative literals
        // and "false" for positive literals. It is called the "sign" bit.
        // TODO: replace parameter 'is_positive' everywhere by 'sign'? (also in signed_constraint)
        sat::bool_var       m_bvar = sat::null_bool_var;

        constraint(constraint_manager& m, unsigned lvl, ckind_t k):
            /*m_manager(&m),*/ m_level(lvl), m_kind(k) {}

    protected:
        std::ostream& display_extra(std::ostream& out, lbool status) const;

    public:
        virtual ~constraint() {}

        virtual unsigned hash() const = 0;
        virtual bool operator==(constraint const& other) const = 0;

        bool is_eq() const { return m_kind == ckind_t::eq_t; }
        bool is_ule() const { return m_kind == ckind_t::ule_t; }
        ckind_t kind() const { return m_kind; }
        virtual std::ostream& display(std::ostream& out, lbool status = l_undef) const = 0;

        bool propagate(solver& s, bool is_positive, pvar v);
        virtual void propagate_core(solver& s, bool is_positive, pvar v, pvar other_v);
        virtual bool is_always_false(bool is_positive) = 0;
        virtual bool is_currently_false(solver& s, bool is_positive) = 0;
        virtual bool is_currently_true(solver& s, bool is_positive) = 0;
        virtual void narrow(solver& s, bool is_positive) = 0;
        virtual inequality as_inequality(bool is_positive) const = 0;

        eq_constraint& to_eq();
        eq_constraint const& to_eq() const;
        ule_constraint& to_ule();
        ule_constraint const& to_ule() const;
        unsigned_vector& vars() { return m_vars; }
        unsigned_vector const& vars() const { return m_vars; }
        unsigned var(unsigned idx) const { return m_vars[idx]; }
        unsigned level() const { return m_level; }
        bool has_bvar() const { return m_bvar != sat::null_bool_var; }
        sat::bool_var bvar() const { return m_bvar; }

        clause* unit_clause() const { return m_unit_clause; }
        void set_unit_clause(clause* cl) { SASSERT(cl); SASSERT(!m_unit_clause || m_unit_clause == cl); m_unit_clause = cl; }
        p_dependency* unit_dep() const { return m_unit_clause ? m_unit_clause->dep() : nullptr; }

        /** Precondition: all variables other than v are assigned.
         *
         * \param[out] out_interval     The forbidden interval for this constraint
         * \param[out] out_neg_cond     Negation of the side condition (the side condition is true when the forbidden interval is trivial). May be NULL if the condition is constant.
         * \returns True iff a forbidden interval exists and the output parameters were set.
         */
        // TODO: we can probably remove this and unify the implementations for both cases by relying on as_inequality().
        virtual bool forbidden_interval(solver& s, bool is_positive, pvar v, eval_interval& out_interval, signed_constraint& out_neg_cond) { return false; }
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
        bool is_always_false() { return get()->is_always_false(is_positive()); }
        bool is_always_true() { return get()->is_always_false(is_negative()); }
        bool is_currently_false(solver& s) { return get()->is_currently_false(s, is_positive()); }
        bool is_currently_true(solver& s) { return get()->is_currently_true(s, is_positive()); }
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

        bool operator==(signed_constraint const& other) const {
            return get() == other.get() && is_positive() == other.is_positive();
        }

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
