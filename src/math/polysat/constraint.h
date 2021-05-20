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
#include "util/map.h"

namespace polysat {

    enum ckind_t { eq_t, ule_t, bit_t };
    enum csign_t : bool { neg_t = false, pos_t = true };

    class constraint;
    class clause;
    class eq_constraint;
    class var_constraint;
    class ule_constraint;

    // Manage constraint lifetime, deduplication, and connection to boolean variables/literals.
    class constraint_manager {
        bool_var_manager& m_bvars;

        // Constraint storage per level
        vector<scoped_ptr_vector<constraint>> m_constraints;

        // Association to boolean variables
        ptr_vector<constraint>   m_bv2constraint;
        void insert_bv2c(bool_var bv, constraint* c) { m_bv2constraint.setx(bv, c, nullptr); }
        void erase_bv2c(bool_var bv) { m_bv2constraint[bv] = nullptr; }
        constraint* get_bv2c(bool_var bv) const { return m_bv2constraint.get(bv, nullptr); }

        // Association to external dependency values (i.e., external names for constraints)
        u_map<constraint*> m_external_constraints;

        // TODO: some hashmaps to look up whether constraint (or its negation) already exists

    public:
        constraint_manager(bool_var_manager& bvars): m_bvars(bvars) {}

        // Start managing lifetime of the given constraint and assign a boolean literal to it.
        bool_lit insert(constraint* c);

        // Release constraints at the given level and above.
        void release_level(unsigned lvl);

        constraint* lookup(bool_lit lit);
        constraint* lookup_external(unsigned dep) { return m_external_constraints.get(dep, nullptr); }

        // // Convenience methods; they automatically insert the constraint.
        // static constraint* eq(unsigned lvl, csign_t sign, pdd const& p, p_dependency_ref const& d);
        // static constraint* viable(unsigned lvl, csign_t sign, pvar v, bdd const& b, p_dependency_ref const& d);
        // static constraint* ule(unsigned lvl, csign_t sign, pdd const& a, pdd const& b, p_dependency_ref const& d);
        // static constraint* ult(unsigned lvl, csign_t sign, pdd const& a, pdd const& b, p_dependency_ref const& d);
        // static constraint* sle(unsigned lvl, csign_t sign, pdd const& a, pdd const& b, p_dependency_ref const& d);
        // static constraint* slt(unsigned lvl, csign_t sign, pdd const& a, pdd const& b, p_dependency_ref const& d);
    };

    class constraint {
        friend class constraint_manager;
        friend class clause;
        friend class var_constraint;
        friend class eq_constraint;
        friend class ule_constraint;
        constraint_manager* m_manager = nullptr;   // TODO
        unsigned         m_storage_level;  ///< Controls lifetime of the constraint object. Always a base level (for external dependencies the level at which it was created, and for others the maximum storage level of its external dependencies).
        unsigned         m_active_level;  ///< Level at which the constraint was activated. Possibly different from m_storage_level because constraints in lemmas may become activated only at a higher level.
        ckind_t          m_kind;
        p_dependency_ref m_dep;
        unsigned_vector  m_vars;
        bool_lit         m_lit = bool_lit::invalid();  ///< boolean literal associated to this constraint; is invalid until assigned by constraint_manager::insert
        csign_t          m_sign;  ///< sign/polarity
        lbool            m_status = l_undef;  ///< current constraint status, computed from value of m_lit and m_sign
        // clause*          m_clause = nullptr;  ///< the lemma which has introduced this constraint. NULL for base-level constraints.
        constraint(unsigned lvl, csign_t sign, p_dependency_ref const& dep, ckind_t k):
            m_storage_level(lvl), m_kind(k), m_dep(dep), m_sign(sign) {}
    public:
        static constraint* eq(unsigned lvl, csign_t sign, pdd const& p, p_dependency_ref const& d);
        static constraint* viable(unsigned lvl, csign_t sign, pvar v, bdd const& b, p_dependency_ref const& d);
        static constraint* ule(unsigned lvl, csign_t sign, pdd const& a, pdd const& b, p_dependency_ref const& d);
        static constraint* ult(unsigned lvl, csign_t sign, pdd const& a, pdd const& b, p_dependency_ref const& d);
        static constraint* sle(unsigned lvl, csign_t sign, pdd const& a, pdd const& b, p_dependency_ref const& d);
        static constraint* slt(unsigned lvl, csign_t sign, pdd const& a, pdd const& b, p_dependency_ref const& d);
        virtual ~constraint() {}
        bool is_eq() const { return m_kind == ckind_t::eq_t; }
        bool is_ule() const { return m_kind == ckind_t::ule_t; }
        bool is_bit() const { return m_kind == ckind_t::bit_t; }
        ckind_t kind() const { return m_kind; }
        virtual std::ostream& display(std::ostream& out) const = 0;
        bool propagate(solver& s, pvar v);
        virtual void propagate_core(solver& s, pvar v, pvar other_v);
        virtual constraint* resolve(solver& s, pvar v) = 0;
        virtual bool is_always_false() = 0;
        virtual bool is_currently_false(solver& s) = 0;
        virtual bool is_currently_true(solver& s) = 0;
        virtual void narrow(solver& s) = 0;
        eq_constraint& to_eq();
        eq_constraint const& to_eq() const;
        ule_constraint& to_ule();
        ule_constraint const& to_ule() const;
        var_constraint& to_bit();
        var_constraint const& to_bit() const;
        p_dependency* dep() const { return m_dep; }
        // clause* clause() const { return m_clause; }
        unsigned_vector& vars() { return m_vars; }
        unsigned_vector const& vars() const { return m_vars; }
        unsigned level() const { return m_storage_level; }
        bool_lit lit() const { return m_lit; }
        bool sign() const { return m_sign; }
        void assign(bool is_true) {
            lbool new_status = (is_true ^ !m_sign) ? l_true : l_false;
            SASSERT(is_undef() || new_status == m_status);
            m_status = new_status;
        }
        void unassign() { m_status = l_undef; }
        bool is_undef() const { return m_status == l_undef; }

        /** Precondition: all variables other than v are assigned.
         *
         * \param[out] out_interval     The forbidden interval for this constraint
         * \param[out] out_neg_cond     Negation of the side condition (the side condition is true when the forbidden interval is trivial). May be NULL if the condition is constant.
         * \returns True iff a forbidden interval exists and the output parameters were set.
         */
        virtual bool forbidden_interval(solver& s, pvar v, eval_interval& out_interval, scoped_ptr<constraint>& out_neg_cond) { return false; }

    protected:
        bool is_positive() const { return m_status == l_true; }
        bool is_negative() const { return m_status == l_false; }
    };

    inline std::ostream& operator<<(std::ostream& out, constraint const& c) { return c.display(out); }

    /*   NOTE: not used at the moment
    class signed_constraint {
        constraint* c;
        csign_t sign;
        // TODO: move sign from constraint to this
    };

    class active_constraint {
        signed_constraint c;
        bool status;
        // TODO: move status from constraint to this
    };
    */

    // NOTE: not used at the moment
    /*
    // A disjunctive lemma:
    //
    //      A_1 /\ ... /\ A_m ==> C_1 \/ ... \/ C_n
    //
    // where
    // - A_i are existing (redundant) constraints in m_antecedents
    // - C_j are new constraints in m_consequents.
    class lemma {
        unsigned m_level;
        p_dependency_ref m_dep;
        ptr_vector<constraint> m_antecedents;
        scoped_ptr_vector<constraint> m_consequents;

    public:
        bool is_unit() const { return m_antecedents.empty() && m_consequents.size() == 1; }
    };
    */

    // A clause of the form:
    //
    //      A_1 /\ ... /\ A_m ==> C_1 \/ ... \/ C_n
    //
    // where
    // - A_i are existing constraints (the first m_num_antecedents constraints in m_literals)
    // - C_j are new constraints (the rest in m_literals)
    class clause {
        unsigned m_level;
        unsigned m_next_guess;  // next guess for enumerative backtracking
        unsigned m_num_antecedents;  // number of negated constraints at the beginning of m_literals
        p_dependency_ref m_dep;
        ptr_vector<constraint> m_literals;

        /* TODO: embed literals to save an indirection?
        unsigned m_num_literals;
        constraint* m_literals[0];

        static size_t object_size(unsigned m_num_literals) {
            return sizeof(clause) + m_num_literals * sizeof(constraint*);
        }
        */

        clause(unsigned lvl, p_dependency_ref const& d, unsigned num_antecedents, ptr_vector<constraint> const& literals):
            m_level(lvl), m_next_guess(num_antecedents), m_num_antecedents(num_antecedents), m_dep(d), m_literals(literals)
        {
            SASSERT(std::all_of(m_literals.begin(), m_literals.end(),
                [this](constraint* c) {
                    return (c != nullptr) && (c->level() <= level());
                }));
            // SASSERT(std::all_of(consequents_begin(), consequents_end(), [this](constraint* c) { return c->clause() == this; }));
        }


    public:
        static clause* unit(constraint* c);
        static clause* from_literals(unsigned lvl, p_dependency_ref const& d, unsigned num_antecedents, ptr_vector<constraint> const& literals);

        // Resolve with 'other' upon 'var'.
        bool resolve(bool_var var, clause const* other);

        ptr_vector<constraint> const& literals() const { return m_literals; }
        p_dependency* dep() const { return m_dep; }
        unsigned level() const { return m_level; }

        bool empty() const { return m_literals.empty(); }
        unsigned size() const { return m_literals.size(); }
        constraint* operator[](unsigned idx) const { return m_literals[idx]; }

        using const_iterator = typename ptr_vector<constraint>::const_iterator;
        const_iterator begin() const { return m_literals.begin(); }
        const_iterator end() const { return m_literals.end(); }
        const_iterator antecedents_begin() const { return m_literals.begin(); }
        const_iterator antecedents_end() const { return m_literals.begin() + m_num_antecedents; }
        const_iterator consequents_begin() const { return m_literals.begin() + m_num_antecedents; }
        const_iterator consequents_end() const { return m_literals.end(); }

        bool is_always_false() const {
            return std::all_of(m_literals.begin(), m_literals.end(), [](constraint* c) { return c->is_always_false(); });
        }

        bool is_currently_false(solver& s) const {
            return std::all_of(m_literals.begin(), m_literals.end(), [&s](constraint* c) { return c->is_currently_false(s); });
        }

        unsigned next_guess() {
            return m_next_guess++;
        }

        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, clause const& c) { return c.display(out); }

    // A clause that owns (some of) its literals
    struct scoped_clause {
        scoped_ptr<clause> clause;
        scoped_ptr_vector<constraint> constraint_storage;

        operator bool() const { return clause; }

        bool is_unit() const { return clause && clause->size() == 1; }
        constraint* unit() const { SASSERT(is_unit()); return (*clause)[0]; }

        bool empty() const { SASSERT(clause); return clause->empty(); }
        unsigned size() const { SASSERT(clause); return clause->size(); }
        constraint* operator[](unsigned idx) const { SASSERT(clause); return (*clause)[idx]; }

        bool is_always_false() const { return clause->is_always_false(); }
        bool is_currently_false(solver& s) const { return clause->is_currently_false(s); }

        polysat::clause* get() { return clause.get(); }
        polysat::clause* detach() { SASSERT(constraint_storage.empty()); return clause.detach(); }
        ptr_vector<constraint> detach_literals() { return constraint_storage.detach(); }

        using const_iterator = typename clause::const_iterator;
        const_iterator begin() const { SASSERT(clause); return clause->begin(); }
        const_iterator end() const { SASSERT(clause); return clause->end(); }

        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, scoped_clause const& c) { return c.display(out); }

    // Container for unit constraints and clauses.
    class constraints_and_clauses {
        ptr_vector<constraint> m_units;
        ptr_vector<clause> m_clauses;

    public:
        ptr_vector<constraint> const& units() const { return m_units; }
        ptr_vector<constraint>& units() { return m_units; }

        ptr_vector<clause> const& clauses() const { return m_clauses; }
        ptr_vector<clause>& clauses() { return m_clauses; }

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
            m_units.append(cs);
        }

        void push_back(std::nullptr_t) {
            m_units.push_back(nullptr);
        }

        void push_back(constraint* c) {
            m_units.push_back(c);
        }

        void push_back(clause* cl) {
            // if (cl->size() == 1) {
            //     // TODO: is this really what we want? (the deps of clause and constraint may be different)
            //     m_units.push_back((*cl)[0]);
            // } else
                m_clauses.push_back(cl);
        }

        // TODO: use iterator instead
        unsigned_vector vars() const {
            unsigned_vector vars;
            for (constraint* c : m_units)
                vars.append(c->vars());
            for (clause* cl : m_clauses)
                for (constraint* c : *cl)
                    vars.append(c->vars());
            return vars;
        }

        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, constraints_and_clauses const& c) { return c.display(out); }

}
