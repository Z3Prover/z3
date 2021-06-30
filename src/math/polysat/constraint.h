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

namespace polysat {

    enum ckind_t { eq_t, ule_t };
    enum csign_t : bool { neg_t = false, pos_t = true };

    class constraint_literal;
    class constraint;
    class constraint_manager;
    class clause;
    class scoped_clause;
    class eq_constraint;
    class ule_constraint;
    using constraint_ref = ref<constraint>;
    using constraint_ref_vector = sref_vector<constraint>;
    using clause_ref = ref<clause>;
    using clause_ref_vector = sref_vector<clause>;

    // Manage constraint lifetime, deduplication, and connection to boolean variables/literals.
    class constraint_manager {
        friend class constraint;

        bool_var_manager& m_bvars;
        // poly_dep_manager& m_dm;

        // Association to boolean variables
        ptr_vector<constraint>   m_bv2constraint;
        void insert_bv2c(sat::bool_var bv, constraint* c) { /* NOTE: will be called with incompletely constructed c! */ m_bv2constraint.setx(bv, c, nullptr); }
        void erase_bv2c(sat::bool_var bv) {  m_bv2constraint[bv] = nullptr; }
        constraint* get_bv2c(sat::bool_var bv) const { return m_bv2constraint.get(bv, nullptr); }

        // Constraint storage per level; should be destructed before m_bv2constraint
        vector<vector<constraint_ref>> m_constraints;
        vector<vector<clause_ref>> m_clauses;

        // Association to external dependency values (i.e., external names for constraints)
        u_map<constraint*> m_external_constraints;

        // TODO: some hashmaps to look up whether constraint (or its negation) already exists

    public:
        constraint_manager(bool_var_manager& bvars): m_bvars(bvars) {}
        // constraint_manager(bool_var_manager& bvars, poly_dep_manager& dm): m_bvars(bvars), m_dm(dm) {}
        ~constraint_manager();

        // Start managing lifetime of the given constraint
        constraint* store(constraint_ref c);
        clause* store(clause_ref cl);

        /// Register a unit clause with an external dependency.
        void register_external(constraint* c);

        /// Release constraints at the given level and above.
        void release_level(unsigned lvl);

        constraint* lookup(sat::bool_var var) const;
        constraint* lookup_external(unsigned dep) const { return m_external_constraints.get(dep, nullptr); }

        constraint_literal eq(unsigned lvl, pdd const& p);
        constraint_literal ule(unsigned lvl, pdd const& a, pdd const& b);
        constraint_literal ult(unsigned lvl, pdd const& a, pdd const& b);
        constraint_literal sle(unsigned lvl, pdd const& a, pdd const& b);
        constraint_literal slt(unsigned lvl, pdd const& a, pdd const& b);

        // p_dependency_ref null_dep() const { return {nullptr, m_dm}; }
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
        friend class scoped_clause;
        friend class eq_constraint;
        friend class ule_constraint;

        constraint_manager* m_manager;
        clause*             m_unit_clause = nullptr;  ///< If this constraint was asserted by a unit clause, we store that clause here.
        unsigned            m_ref_count = 0;
        // TODO: we could remove the level on constraints and instead store constraint_refs for all literals inside the clause? (clauses will then be 4 times larger though...)
        unsigned            m_storage_level;  ///< Controls lifetime of the constraint object. Always a base level.
        ckind_t             m_kind;
        unsigned_vector     m_vars;
        sat::bool_var       m_bvar;  ///< boolean variable associated to this constraint; convention: a constraint itself always represents the positive sat::literal
        lbool               m_status = l_undef;  ///< current constraint status; intended to be the same as m_manager->m_bvars.value(bvar()) if that value is set.

        constraint(constraint_manager& m, unsigned lvl, ckind_t k):
            m_manager(&m), m_storage_level(lvl), m_kind(k), m_bvar(m_manager->m_bvars.new_var()) {
            SASSERT_EQ(m_manager->get_bv2c(bvar()), nullptr);
            m_manager->insert_bv2c(bvar(), this);
        }

    protected:
        std::ostream& display_extra(std::ostream& out) const;

    public:
        void inc_ref() { m_ref_count++; }
        void dec_ref() { SASSERT(m_ref_count > 0); m_ref_count--; if (!m_ref_count) dealloc(this); }
        virtual ~constraint() {
            SASSERT_EQ(m_manager->get_bv2c(bvar()), this);
            m_manager->erase_bv2c(bvar());
            m_manager->m_bvars.del_var(m_bvar);
        }

        bool is_eq() const { return m_kind == ckind_t::eq_t; }
        bool is_ule() const { return m_kind == ckind_t::ule_t; }
        ckind_t kind() const { return m_kind; }
        virtual std::ostream& display(std::ostream& out) const = 0;
        bool propagate(solver& s, pvar v);
        virtual void propagate_core(solver& s, pvar v, pvar other_v);
        virtual bool is_always_false() = 0;
        virtual bool is_currently_false(solver& s) = 0;
        virtual bool is_currently_true(solver& s) = 0;
        virtual void narrow(solver& s) = 0;
        virtual inequality as_inequality() const = 0;
        eq_constraint& to_eq();
        eq_constraint const& to_eq() const;
        ule_constraint& to_ule();
        ule_constraint const& to_ule() const;
        unsigned_vector& vars() { return m_vars; }
        unsigned_vector const& vars() const { return m_vars; }
        unsigned level() const { return m_storage_level; }
        // unsigned active_level() const {
        //     SASSERT(!is_undef());
        //     return m_manager->m_bvars.level(bvar());
        // }
        // unsigned active_at_base_level(solver& s) const {
        //     return !is_undef() && active_level() <= s.base_level();
        // }
        sat::bool_var bvar() const { return m_bvar; }

        sat::literal blit() const { SASSERT(!is_undef()); return m_status == l_true ? sat::literal(m_bvar) : ~sat::literal(m_bvar); }
        void assign(bool is_true) {
            SASSERT(m_status == l_undef /* || m_status == to_lbool(is_true) */);
            m_status = to_lbool(is_true);
            // SASSERT(m_manager->m_bvars.value(bvar()) == l_undef || m_manager->m_bvars.value(bvar()) == m_status);  // TODO: is this always true? maybe we sometimes want to check the opposite phase temporarily.
        }
        void unassign() { m_status = l_undef; }
        bool is_undef() const { return m_status == l_undef; }
        bool is_positive() const { return m_status == l_true; }
        bool is_negative() const { return m_status == l_false; }

        clause* unit_clause() const { return m_unit_clause; }
        void set_unit_clause(clause* cl) { SASSERT(cl); SASSERT(!m_unit_clause); m_unit_clause = cl; }
        p_dependency* unit_dep() const;

        /** Precondition: all variables other than v are assigned.
         *
         * \param[out] out_interval     The forbidden interval for this constraint
         * \param[out] out_neg_cond     Negation of the side condition (the side condition is true when the forbidden interval is trivial). May be NULL if the condition is constant.
         * \returns True iff a forbidden interval exists and the output parameters were set.
         */
        virtual bool forbidden_interval(solver& s, pvar v, eval_interval& out_interval, constraint_literal& out_neg_cond) { return false; }
    };

    inline std::ostream& operator<<(std::ostream& out, constraint const& c) { return c.display(out); }


    /// Literal together with the constraint it represents.
    /// (or: constraint with polarity)
    class constraint_literal {
        sat::literal m_literal = sat::null_literal;
        constraint_ref m_constraint = nullptr;

    public:
        constraint_literal() {}
        constraint_literal(sat::literal lit, constraint_ref c):
            m_literal(lit), m_constraint(std::move(c)) {
            SASSERT(get());
            SASSERT(literal().var() == get()->bvar());
        }
        constraint_literal operator~() const&& {
            return {~m_literal, std::move(m_constraint)};
        }
        sat::literal literal() const { return m_literal; }
        constraint* get() const { return m_constraint.get(); }
        constraint_ref detach() { m_literal = sat::null_literal; return std::move(m_constraint); }

        explicit operator bool() const { return !!m_constraint; }
        bool operator!() const { return !m_constraint; }
        polysat::constraint* operator->() const { return m_constraint.get(); }
        polysat::constraint const& operator*() const { return *m_constraint; }

        constraint_literal& operator=(nullptr_t) { m_literal = sat::null_literal; m_constraint = nullptr; return *this; }
    private:
        friend class constraint_manager;
        explicit constraint_literal(polysat::constraint* c): constraint_literal(sat::literal(c->bvar()), c) {}
    };


    /// Disjunction of constraints represented by boolean literals
    class clause {
        friend class constraint_manager;

        unsigned m_ref_count = 0;
        unsigned m_level;
        unsigned m_next_guess = 0;  // next guess for enumerative backtracking
        p_dependency_ref m_dep;
        sat::literal_vector m_literals;
        constraint_ref_vector m_new_constraints;  // new constraints, temporarily owned by this clause

        /* TODO: embed literals to save an indirection?
        unsigned m_num_literals;
        constraint* m_literals[0];

        static size_t object_size(unsigned m_num_literals) {
            return sizeof(clause) + m_num_literals * sizeof(constraint*);
        }
        */

        clause(unsigned lvl, p_dependency_ref d, sat::literal_vector literals, constraint_ref_vector new_constraints):
            m_level(lvl), m_dep(std::move(d)), m_literals(std::move(literals)), m_new_constraints(std::move(new_constraints))
        {
            SASSERT(std::count(m_literals.begin(), m_literals.end(), sat::null_literal) == 0);
        }

    public:
        void inc_ref() { m_ref_count++; }
        void dec_ref() { SASSERT(m_ref_count > 0); m_ref_count--; if (!m_ref_count) dealloc(this); }

        static clause_ref from_unit(constraint_literal c, p_dependency_ref d);
        static clause_ref from_literals(unsigned lvl, p_dependency_ref d, sat::literal_vector literals, constraint_ref_vector new_constraints);

        // Resolve with 'other' upon 'var'.
        bool resolve(sat::bool_var var, clause const& other);

        sat::literal_vector const& literals() const { return m_literals; }
        p_dependency* dep() const { return m_dep; }
        unsigned level() const { return m_level; }

        constraint_ref_vector const& new_constraints() const { return m_new_constraints; }
        bool empty() const { return m_literals.empty(); }
        unsigned size() const { return m_literals.size(); }
        sat::literal operator[](unsigned idx) const { return m_literals[idx]; }

        using const_iterator = typename sat::literal_vector::const_iterator;
        const_iterator begin() const { return m_literals.begin(); }
        const_iterator end() const { return m_literals.end(); }

        bool is_always_false(solver& s) const;
        bool is_currently_false(solver& s) const;

        unsigned next_guess() {
            SASSERT(m_next_guess < m_literals.size());
            return m_next_guess++;
        }

        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, clause const& c) { return c.display(out); }


    // Container for unit constraints and clauses.
    class constraints_and_clauses {
        constraint_ref_vector m_units;
        clause_ref_vector m_clauses;

    public:
        constraint_ref_vector const& units() const { return m_units; }
        constraint_ref_vector& units() { return m_units; }

        clause_ref_vector const& clauses() const { return m_clauses; }
        clause_ref_vector& clauses() { return m_clauses; }

        bool is_unit() const { return units().size() == 1 && clauses().empty(); }
        constraint* get_unit() const { SASSERT(is_unit()); return units()[0]; }

        bool is_clause() const { return units().empty() && clauses().size() == 1; }
        clause* get_clause() const { SASSERT(is_clause()); return clauses()[0]; }

        unsigned size() const {
            return m_units.size() + m_clauses.size();
        }

        bool empty() const {
            return m_units.empty() && m_clauses.empty();
        }

        void reset() {
            m_units.reset();
            m_clauses.reset();
        }

        void append(ptr_vector<constraint> const& cs) {
            for (constraint* c : cs)
                m_units.push_back(c);
        }

        void push_back(std::nullptr_t) { m_units.push_back(nullptr); }
        void push_back(constraint_ref c) { m_units.push_back(std::move(c)); }
        void push_back(clause_ref cl) { m_clauses.push_back(std::move(cl)); }

        // TODO: use iterator instead
        unsigned_vector vars(constraint_manager const& cm) const {
            unsigned_vector vars;
            for (auto const& c : m_units)
                vars.append(c->vars());
            for (auto const& cl : m_clauses)
                for (auto lit : *cl) {
                    constraint* c = cm.lookup(lit.var());
                    if (c)
                        vars.append(c->vars());
                }
            return vars;
        }

        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, constraints_and_clauses const& c) { return c.display(out); }


    /// Temporarily assign a constraint according to the sign of the given literal.
    class tmp_assign final {
        constraint* m_constraint;
        bool m_should_unassign = false;
    public:
        tmp_assign(constraint* c, sat::literal lit):
            m_constraint(c) {
            SASSERT(c);
            SASSERT_EQ(c->bvar(), lit.var());
            if (c->is_undef()) {
                c->assign(!lit.sign());
                m_should_unassign = true;
            }
            else
                SASSERT_EQ(c->blit(), lit);
        }
        tmp_assign(constraint_ref const& c, sat::literal lit): tmp_assign(c.get(), lit) {}
        void revert() {
            if (m_should_unassign) {
                m_constraint->unassign();
                m_should_unassign = false;
            }
        }
        ~tmp_assign() {
            revert();
        }
        tmp_assign(tmp_assign&) = delete;
        tmp_assign(tmp_assign&&) = delete;
        tmp_assign& operator=(tmp_assign&) = delete;
        tmp_assign& operator=(tmp_assign&&) = delete;
    };

    inline p_dependency* constraint::unit_dep() const { return m_unit_clause ? m_unit_clause->dep() : nullptr; }
}
