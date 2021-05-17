/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat constraints

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/polysat/types.h"
#include "math/polysat/interval.h"

namespace polysat {

    enum ckind_t { eq_t, ule_t, sle_t, bit_t };
    enum csign_t : bool { neg_t = false, pos_t = true };

    class eq_constraint;
    class var_constraint;
    class ule_constraint;

    class constraint {
        friend class var_constraint;
        friend class eq_constraint;
        friend class ule_constraint;
        unsigned         m_level;
        ckind_t          m_kind;
        p_dependency_ref m_dep;
        unsigned_vector  m_vars;
        bool_var         m_bool_var;
        csign_t          m_sign;  ///< sign/polarity
        lbool            m_status = l_undef;  ///< current constraint status, computed from value of m_bool_var and m_sign
        constraint(unsigned lvl, bool_var bvar, csign_t sign, p_dependency_ref const& dep, ckind_t k):
            m_level(lvl), m_kind(k), m_dep(dep), m_bool_var(bvar), m_sign(sign) {}
    public:
        static constraint* eq(unsigned lvl, bool_var bvar, csign_t sign, pdd const& p, p_dependency_ref const& d);
        static constraint* viable(unsigned lvl, bool_var bvar, csign_t sign, pvar v, bdd const& b, p_dependency_ref const& d);
        static constraint* ule(unsigned lvl, bool_var bvar, csign_t sign, pdd const& a, pdd const& b, p_dependency_ref const& d);
        static constraint* ult(unsigned lvl, bool_var bvar, csign_t sign, pdd const& a, pdd const& b, p_dependency_ref const& d);
        virtual ~constraint() {}
        bool is_eq() const { return m_kind == ckind_t::eq_t; }
        bool is_ule() const { return m_kind == ckind_t::ule_t; }
        bool is_sle() const { return m_kind == ckind_t::sle_t; }
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
        p_dependency* dep() const { return m_dep; }
        unsigned_vector& vars() { return m_vars; }
        unsigned level() const { return m_level; }
        bool_var bvar() const { return m_bool_var; }
        bool sign() const { return m_sign; }
        void assign_eh(bool is_true) { m_status = (is_true ^ !m_sign) ? l_true : l_false; }
        void unassign_eh() { m_status = l_undef; }
        bool is_positive() const { return m_status == l_true; }
        bool is_negative() const { return m_status == l_false; }
        bool is_undef() const { return m_status == l_undef; }

        /** Precondition: all variables other than v are assigned.
         *
         * \param[out] out_interval     The forbidden interval for this constraint
         * \param[out] out_neg_cond     Negation of the side condition (the side condition is true when the forbidden interval is trivial). May be NULL if the condition is constant.
         * \returns True iff a forbidden interval exists and the output parameters were set.
         */
        virtual bool forbidden_interval(solver& s, pvar v, eval_interval& out_interval, scoped_ptr<constraint>& out_neg_cond) { return false; }
    };

    inline std::ostream& operator<<(std::ostream& out, constraint const& c) { return c.display(out); }

    class clause {
        unsigned m_level;
        p_dependency_ref m_dep;
        ptr_vector<constraint> m_literals;

        /* TODO: embed literals to save an indirection?
        unsigned m_num_literals;
        constraint* m_literals[0];

        static size_t object_size(unsigned m_num_literals) {
            return sizeof(clause) + m_num_literals * sizeof(constraint*);
        }
        */

        clause(unsigned lvl, p_dependency_ref const& d, ptr_vector<constraint> const& literals):
            m_level(lvl), m_dep(d), m_literals(literals)
        {
            SASSERT(std::all_of(m_literals.begin(), m_literals.end(),
                [this](constraint *c) {
                    return (c != nullptr) && (c->level() <= level());
                }));
        }

    public:
        static clause* from_literals(unsigned lvl, p_dependency_ref const& d, ptr_vector<constraint> const& literals);

        ptr_vector<constraint> const literals() const { return m_literals; }
        p_dependency* dep() const { return m_dep; }
        unsigned level() const { return m_level; }

        bool empty() const { return m_literals.empty(); }
        unsigned size() const { return m_literals.size(); }
        constraint* operator[](unsigned idx) const { return m_literals[idx]; }

        using const_iterator = typename ptr_vector<constraint>::const_iterator;
        const_iterator begin() const { return m_literals.begin(); }
        const_iterator end() const { return m_literals.end(); }
    };

    // A clause that owns (some of) its literals
    struct scoped_clause {
        scoped_ptr<clause> clause;
        scoped_ptr_vector<constraint> constraint_storage;
    };


}
