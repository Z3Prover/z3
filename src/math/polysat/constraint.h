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
#include "math/polysat/types.h"
#include "math/polysat/interval.h"
#include "math/polysat/log.h"
#include "util/map.h"
#include "util/ref.h"
#include "util/ref_vector.h"
#include <type_traits>

namespace polysat {

    enum ckind_t { eq_t, ule_t };

    class constraint;
    class eq_constraint;
    class ule_constraint;

    class scoped_constraint_ptr;

    template <bool is_owned>
    class signed_constraint_base;
    using signed_constraint = signed_constraint_base<false>;
    using scoped_signed_constraint = signed_constraint_base<true>;

    class clause;
    using clause_ref = ref<clause>;
    using clause_ref_vector = sref_vector<clause>;

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

        void assign_bvar(constraint* c);
        void erase_bvar(constraint* c);
        sat::literal get_or_assign_blit(signed_constraint& c);

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

        scoped_signed_constraint eq(unsigned lvl, pdd const& p);
        scoped_signed_constraint ule(unsigned lvl, pdd const& a, pdd const& b);
        scoped_signed_constraint ult(unsigned lvl, pdd const& a, pdd const& b);
        scoped_signed_constraint sle(unsigned lvl, pdd const& a, pdd const& b);
        scoped_signed_constraint slt(unsigned lvl, pdd const& a, pdd const& b);
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
        p_dependency* unit_dep() const;

        /** Precondition: all variables other than v are assigned.
         *
         * \param[out] out_interval     The forbidden interval for this constraint
         * \param[out] out_neg_cond     Negation of the side condition (the side condition is true when the forbidden interval is trivial). May be NULL if the condition is constant.
         * \returns True iff a forbidden interval exists and the output parameters were set.
         */
        // TODO: we can probably remove this and unify the implementations for both cases by relying on as_inequality().
        virtual bool forbidden_interval(solver& s, bool is_positive, pvar v, eval_interval& out_interval, scoped_signed_constraint& out_neg_cond) { return false; }
    };

    inline std::ostream& operator<<(std::ostream& out, constraint const& c) { return c.display(out); }


    // Like scoped_ptr<constraint>, but only deallocates the constraint if it is temporary (i.e., does not have a boolean variable).
    // This is needed because when a constraint is created, due to deduplication, we might get either a new constraint or an existing one.
    // (We want early deduplication because otherwise we might overlook possible boolean resolutions during conflict resolution.)
    // (TODO: we could replace this class by std::unique_ptr with a custom deleter)
    class scoped_constraint_ptr {
        constraint* m_ptr;

        void dealloc_ptr() const {
            if (m_ptr && !m_ptr->has_bvar())
                dealloc(m_ptr);
        }

    public:
        scoped_constraint_ptr(constraint* ptr = nullptr): m_ptr(ptr) {}

        scoped_constraint_ptr(scoped_constraint_ptr &&other) noexcept : m_ptr(nullptr) {
            std::swap(m_ptr, other.m_ptr);
        }

        ~scoped_constraint_ptr() {
            dealloc_ptr();
        }

        scoped_constraint_ptr& operator=(scoped_constraint_ptr&& other) {
            *this = other.detach();
            return *this;
        };

        scoped_constraint_ptr& operator=(constraint* n) {
            if (m_ptr != n) {
                dealloc_ptr();
                m_ptr = n;
            }
            return *this;
        }

        void swap(scoped_constraint_ptr& p) {
            std::swap(m_ptr, p.m_ptr);
        }

        constraint* detach() {
            constraint* tmp = m_ptr;
            m_ptr = nullptr;
            return tmp;
        }

        explicit operator bool() const { return !!m_ptr; }
        bool operator!() const { return !m_ptr; }
        constraint* get() const { return m_ptr; }
        constraint* operator->() const { return m_ptr; }
        const constraint& operator*() const { return *m_ptr; }
        constraint &operator*() { return *m_ptr; }
    };


    template <bool is_owned>
    class signed_constraint_base final {
    public:
        using ptr_t = std::conditional_t<is_owned, scoped_constraint_ptr, constraint*>;

    private:
        ptr_t m_constraint = nullptr;
        bool m_positive = true;

    public:
        signed_constraint_base() {}
        signed_constraint_base(constraint* c, bool is_positive):
            m_constraint(c), m_positive(is_positive) {}
        signed_constraint_base(constraint* c, sat::literal lit):
            signed_constraint_base(c, !lit.sign()) {
            SASSERT_EQ(blit(), lit);
        }

        void negate() {
            m_positive = !m_positive;
        }

        bool is_positive() const { return m_positive; }
        bool is_negative() const { return !is_positive(); }

        bool propagate(solver& s, pvar v) { return get()->propagate(s, is_positive(), v); }
        void propagate_core(solver& s, pvar v, pvar other_v) { get()->propagate_core(s, is_positive(), v, other_v); }
        bool is_always_false() { return get()->is_always_false(is_positive()); }
        bool is_currently_false(solver& s) { return get()->is_currently_false(s, is_positive()); }
        bool is_currently_true(solver& s) { return get()->is_currently_true(s, is_positive()); }
        void narrow(solver& s) { get()->narrow(s, is_positive()); }
        inequality as_inequality() const { return get()->as_inequality(is_positive()); }

        sat::bool_var bvar() const { return m_constraint->bvar(); }
        sat::literal blit() const { return sat::literal(bvar(), is_negative()); }
        constraint* get() const { if constexpr (is_owned) return m_constraint.get(); else return m_constraint; }
        signed_constraint get_signed() const { return {get(), m_positive}; }
        template <bool Owned = is_owned>
        std::enable_if_t<Owned, constraint*> detach() { return m_constraint.detach(); }

        explicit operator bool() const { return !!m_constraint; }
        bool operator!() const { return !m_constraint; }
        constraint* operator->() const { return get(); }
        constraint& operator*() { return *m_constraint; }
        constraint const& operator*() const { return *m_constraint; }

        signed_constraint_base<is_owned>& operator=(std::nullptr_t) { m_constraint = nullptr; return *this; }

        bool operator==(signed_constraint_base<is_owned> const& other) const {
            return get() == other.get() && is_positive() == other.is_positive();
        }

        std::ostream& display(std::ostream& out) const {
            if (m_constraint)
                return m_constraint->display(out, to_lbool(is_positive()));
            else
                return out << "<null>";
        }
    };

    template <bool is_owned>
    inline std::ostream& operator<<(std::ostream& out, signed_constraint_base<is_owned> const& c) {
        return c.display(out);
    }

    inline signed_constraint operator~(signed_constraint const& c) {
        return {c.get(), !c.is_positive()};
    }

    inline scoped_signed_constraint operator~(scoped_signed_constraint&& c) {
        return {c.detach(), !c.is_positive()};
    }

    /// Disjunction of constraints represented by boolean literals
    // NB code review:
    // right, ref-count is unlikely the right mechanism.
    // In the SAT solver all clauses are managed in one arena (auxiliarary and redundant)
    // and deleted when they exist the arena.
    //
    class clause {
        friend class constraint_manager;

        unsigned m_ref_count = 0;  // TODO: remove refcount once we confirm it's not needed anymore
        unsigned m_level;
        unsigned m_next_guess = 0;  // next guess for enumerative backtracking
        p_dependency_ref m_dep;
        sat::literal_vector m_literals;

        /* TODO: embed literals to save an indirection?
        unsigned m_num_literals;
        constraint* m_literals[0];

        static size_t object_size(unsigned m_num_literals) {
            return sizeof(clause) + m_num_literals * sizeof(constraint*);
        }
        */

        clause(unsigned lvl, p_dependency_ref d, sat::literal_vector literals):
            m_level(lvl), m_dep(std::move(d)), m_literals(std::move(literals)) {
            SASSERT(std::count(m_literals.begin(), m_literals.end(), sat::null_literal) == 0);
        }

    public:
        void inc_ref() { m_ref_count++; }
        void dec_ref() { SASSERT(m_ref_count > 0); m_ref_count--; if (!m_ref_count) dealloc(this); }

        static clause_ref from_unit(signed_constraint c, p_dependency_ref d);
        static clause_ref from_literals(unsigned lvl, p_dependency_ref d, sat::literal_vector literals);

        p_dependency* dep() const { return m_dep; }
        unsigned level() const { return m_level; }

        bool empty() const { return m_literals.empty(); }
        unsigned size() const { return m_literals.size(); }
        sat::literal operator[](unsigned idx) const { return m_literals[idx]; }

        using const_iterator = typename sat::literal_vector::const_iterator;
        const_iterator begin() const { return m_literals.begin(); }
        const_iterator end() const { return m_literals.end(); }

        bool is_always_false(solver& s) const;
        bool is_currently_false(solver& s) const;

        unsigned next_guess() {
            SASSERT(m_next_guess < size());
            return m_next_guess++;
        }

        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, clause const& c) { return c.display(out); }

    inline p_dependency* constraint::unit_dep() const { return m_unit_clause ? m_unit_clause->dep() : nullptr; }
}
