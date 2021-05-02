/*++
Copyright (c) 2017 Microsoft Corporation

Author:

    Lev Nachmanson (levnach)
    Nikolaj Bjorner (nbjorner)

--*/
#pragma once

#include "util/inf_rational.h"
#include "util/optional.h"

namespace lp_api {

    typedef int bool_var;
    typedef int theory_var;

    enum bound_kind { lower_t, upper_t };

    inline std::ostream& operator<<(std::ostream& out, bound_kind const& k) {
        switch (k) {
        case lower_t: return out << "<=";
        case upper_t: return out << ">=";
        }
        return out;
    }

    template<typename Literal>
    class bound {
        Literal          m_bv;
        theory_var       m_var;
        lp::lpvar        m_vi;
        bool             m_is_int;
        rational         m_value;
        bound_kind       m_bound_kind;
        lp::constraint_index m_constraints[2];

    public:
        bound(Literal bv, theory_var v, lp::lpvar vi, bool is_int, rational const& val, bound_kind k, lp::constraint_index ct, lp::constraint_index cf) :
            m_bv(bv),
            m_var(v),
            m_vi(vi),
            m_is_int(is_int),
            m_value(val),
            m_bound_kind(k) {
            m_constraints[0] = cf;
            m_constraints[1] = ct;
        }

        virtual ~bound() {}

        theory_var get_var() const { return m_var; }

        lp::tv tv() const { return lp::tv::raw(m_vi); }

        Literal get_lit() const { return m_bv; }        

        bound_kind get_bound_kind() const { return m_bound_kind; }

        bool is_int() const { return m_is_int; }

        rational const& get_value() const { return m_value; }

        lp::constraint_index get_constraint(bool b) const { return m_constraints[b]; }

        inf_rational get_value(bool is_true) const {
            if (is_true != get_lit().sign()) 
                return inf_rational(m_value);                         // v >= value or v <= value
            if (m_is_int) {
                SASSERT(m_value.is_int());
                rational const& offset = (m_bound_kind == lower_t) ? rational::minus_one() : rational::one();
                return inf_rational(m_value + offset); // v <= value - 1 or v >= value + 1
            }
            else {
                return inf_rational(m_value, m_bound_kind != lower_t);  // v <= value - epsilon or v >= value + epsilon
            }
        }

        virtual std::ostream& display(std::ostream& out) const {
            return out << m_value << "  " << get_bound_kind() << " v" << get_var();
        }
    };

    template<typename Literal>
    inline std::ostream& operator<<(std::ostream& out, bound<Literal> const& b) {
        return b.display(out);
    }


    typedef optional<inf_rational> opt_inf_rational;


    struct stats {
        unsigned m_assert_lower;
        unsigned m_assert_upper;
        unsigned m_bounds_propagations;
        unsigned m_num_iterations;
        unsigned m_num_iterations_with_no_progress;
        unsigned m_need_to_solve_inf;
        unsigned m_fixed_eqs;
        unsigned m_conflicts;
        unsigned m_bound_propagations1;
        unsigned m_bound_propagations2;
        unsigned m_assert_diseq;
        unsigned m_assert_eq;
        unsigned m_gomory_cuts;
        unsigned m_assume_eqs;
        unsigned m_branch;
        stats() { reset(); }
        void reset() {
            memset(this, 0, sizeof(*this));
        }
        void collect_statistics(statistics& st) const {
            st.update("arith-lower", m_assert_lower);
            st.update("arith-upper", m_assert_upper);
            st.update("arith-propagations", m_bounds_propagations);
            st.update("arith-iterations", m_num_iterations);
            st.update("arith-pivots", m_need_to_solve_inf);
            st.update("arith-plateau-iterations", m_num_iterations_with_no_progress);
            st.update("arith-fixed-eqs", m_fixed_eqs);
            st.update("arith-conflicts", m_conflicts);
            st.update("arith-bound-propagations-lp", m_bound_propagations1);
            st.update("arith-bound-propagations-cheap", m_bound_propagations2);
            st.update("arith-diseq", m_assert_diseq);
            st.update("arith-eq",    m_assert_eq);
            st.update("arith-gomory-cuts", m_gomory_cuts);
            st.update("arith-assume-eqs", m_assume_eqs);
            st.update("arith-branch", m_branch);
        }
    };


}
