/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat constraints

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#pragma once
#include "math/polysat/boolean.h"
#include "math/polysat/types.h"
#include "math/polysat/interval.h"
#include "math/polysat/assignment.h"
#include "math/polysat/univariate/univariate_solver.h"
#include <iostream>

namespace polysat {

    enum ckind_t { ule_t, umul_ovfl_t, smul_fl_t, op_t };

    class constraint_manager;
    class constraint;
    class ule_constraint;
    class umul_ovfl_constraint;
    class smul_fl_constraint;
    class op_constraint;
    class signed_constraint;

    using constraints = ptr_vector<constraint>;
    using signed_constraints = vector<signed_constraint>;

    class constraint {
        friend class constraint_manager;
        friend class signed_constraint;
        friend class clause;
        friend class ule_constraint;
        friend class umul_ovfl_constraint;
        friend class smul_fl_constraint;
        friend class op_constraint;

        ckind_t             m_kind;
        unsigned_vector     m_vars;
        lbool               m_external_sign = l_undef;
        bool                m_is_pwatched = false;
        /** The boolean variable associated to this constraint */
        sat::bool_var       m_bvar = sat::null_bool_var;

        constraint(constraint_manager& m, ckind_t k): m_kind(k) {}

        bool has_bvar() const { return m_bvar != sat::null_bool_var; }

    public:
        virtual ~constraint() {}

        virtual unsigned hash() const = 0;
        virtual bool operator==(constraint const& other) const = 0;
        bool operator!=(constraint const& other) const { return !operator==(other); }

        virtual bool is_eq() const { return false; }
        bool is_ule() const { return m_kind == ckind_t::ule_t; }
        bool is_umul_ovfl() const { return m_kind == ckind_t::umul_ovfl_t; }
        bool is_smul_fl() const { return m_kind == ckind_t::smul_fl_t; }
        bool is_op() const { return m_kind == ckind_t::op_t; }
        ckind_t kind() const { return m_kind; }
        virtual std::ostream& display(std::ostream& out, lbool status) const = 0;
        virtual std::ostream& display(std::ostream& out) const = 0;

        /** Evaluate the positive-polarity constraint under the empty assignment */
        virtual lbool eval() const = 0;
        /** Evaluate the positive-polarity constraint under the given assignment */
        virtual lbool eval(assignment const& a) const = 0;
        /** Evaluate the positive-polarity constraint under the solver's current assignment */
        lbool eval(solver const& s) const;
        bool is_always_true(bool is_positive) const { return eval() == to_lbool(is_positive); }
        bool is_always_false(bool is_positive) const { return is_always_true(!is_positive); }
        bool is_currently_true(assignment const& a, bool is_positive) const { return eval(a) == to_lbool(is_positive); }
        bool is_currently_false(assignment const& a, bool is_positive) const { return is_currently_true(a, !is_positive); }
        bool is_currently_true(solver const& s, bool is_positive) const { return eval(s) == to_lbool(is_positive); }
        bool is_currently_false(solver const& s, bool is_positive) const { return is_currently_true(s, !is_positive); }

        virtual void narrow(solver& s, bool is_positive, bool first) = 0;
        /**
         * If possible, produce a lemma that contradicts the given assignment.
         * This method should not modify the solver's search state.
         * TODO: don't pass the solver, but an interface that only allows creation of constraints
         */
        virtual clause_ref produce_lemma(solver& s, assignment const& a, bool is_positive) { return {}; }

        ule_constraint& to_ule();
        ule_constraint const& to_ule() const;
        umul_ovfl_constraint& to_umul_ovfl();
        umul_ovfl_constraint const& to_umul_ovfl() const;
        smul_fl_constraint& to_smul_fl();
        smul_fl_constraint const& to_smul_fl() const;
        op_constraint& to_op();
        op_constraint const& to_op() const;
        unsigned_vector& vars() { return m_vars; }
        unsigned_vector const& vars() const { return m_vars; }
        unsigned var(unsigned idx) const { return m_vars[idx]; }
        bool contains_var(pvar v) const { return m_vars.contains(v); }
        sat::bool_var bvar() const { SASSERT(has_bvar()); return m_bvar; }
        std::string bvar2string() const;

        void set_external(bool sign) { m_external_sign = to_lbool(sign); }
        void unset_external() { m_external_sign = l_undef; }
        bool is_external() const { return m_external_sign != l_undef; }
        bool external_sign() const { SASSERT(is_external()); return m_external_sign == l_true; }

        bool is_pwatched() const { return m_is_pwatched; }
        void set_pwatched(bool f) { m_is_pwatched = f; }

        /// Assuming the constraint is univariate under the current assignment of 's',
        /// adds the constraint to the univariate solver 'us'.
        virtual void add_to_univariate_solver(solver& s, univariate_solver& us, unsigned dep, bool is_positive) const = 0;
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
        signed_constraint negated() const { return {get(), !is_positive()}; }
        signed_constraint operator~() const { return negated(); }

        bool is_positive() const { return m_positive; }
        bool is_negative() const { return !is_positive(); }

        /** Evaluate the constraint under the empty assignment */
        lbool eval() const { return is_positive() ? get()->eval() : ~get()->eval(); }
        /** Evaluate the constraint under the given assignment */
        lbool eval(assignment const& a) const  { return is_positive() ? get()->eval(a) : ~get()->eval(a); }
        /** Evaluate the constraint under the solver's current assignment */
        lbool eval(solver const& s) const  { return is_positive() ? get()->eval(s) : ~get()->eval(s); }
        bool is_always_false() const { return get()->is_always_false(is_positive()); }
        bool is_always_true() const { return get()->is_always_true(is_positive()); }
        bool is_currently_false(assignment const& a) const { return get()->is_currently_false(a, is_positive()); }
        bool is_currently_true(assignment const& a) const { return get()->is_currently_true(a, is_positive()); }
        bool is_currently_false(solver const& s) const { return get()->is_currently_false(s, is_positive()); }
        bool is_currently_true(solver const& s) const { return get()->is_currently_true(s, is_positive()); }
        lbool bvalue(solver& s) const;
        void narrow(solver& s, bool first) { get()->narrow(s, is_positive(), first); }
        clause_ref produce_lemma(solver& s, assignment const& a) { return get()->produce_lemma(s, a, is_positive()); }

        void add_to_univariate_solver(solver& s, univariate_solver& us, unsigned dep) const { get()->add_to_univariate_solver(s, us, dep, is_positive()); }

        unsigned_vector const& vars() const { return m_constraint->vars(); }
        unsigned var(unsigned idx) const { return m_constraint->var(idx); }
        bool contains_var(pvar v) const { return m_constraint->contains_var(v); }

        sat::bool_var bvar() const { return m_constraint->bvar(); }
        sat::literal blit() const { return sat::literal(bvar(), is_negative()); }
        constraint* get() const { return m_constraint; }

        explicit operator bool() const { return !!m_constraint; }
        bool operator!() const { return !m_constraint; }
        constraint* operator->() const { return get(); }
        constraint& operator*() { return *m_constraint; }
        constraint const& operator*() const { return *m_constraint; }

        bool is_eq() const;
        bool is_diseq() const { return negated().is_eq(); }
        pdd const& eq() const;
        pdd const& diseq() const { return negated().eq(); }

        signed_constraint& operator=(std::nullptr_t) { m_constraint = nullptr; return *this; }

        unsigned hash() const {
            return combine_hash(get_ptr_hash(get()), bool_hash()(is_positive()));
        }
        bool operator==(signed_constraint const& other) const {
            SASSERT_EQ(blit() == other.blit(), get() == other.get() && is_positive() == other.is_positive());
            return blit() == other.blit();
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

    /// Normalized inequality:
    ///     lhs <= rhs, if !is_strict
    ///     lhs < rhs, otherwise
    class inequality {
        pdd m_lhs;
        pdd m_rhs;
        signed_constraint m_src;

        inequality(pdd lhs, pdd rhs, signed_constraint src):
            m_lhs(std::move(lhs)), m_rhs(std::move(rhs)), m_src(std::move(src)) {}

    public:
        static inequality from_ule(signed_constraint src);
        pdd const& lhs() const { return m_lhs; }
        pdd const& rhs() const { return m_rhs; }
        bool is_strict() const { return m_src.is_negative(); }
        signed_constraint as_signed_constraint() const { return m_src; }
    };

    class constraint_pp {
        constraint const* c;
        lbool status;
    public:
        constraint_pp(constraint const* c, lbool status): c(c), status(status) {}
        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, constraint_pp const& p) { return p.display(out); }

    inline std::ostream& operator<<(std::ostream& out, inequality const& i) { return out << i.as_signed_constraint(); }

}
