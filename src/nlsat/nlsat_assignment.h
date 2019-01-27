/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_assignment.h

Abstract:

    Assignment: Var -> Algebraic Number 

Author:

    Leonardo de Moura (leonardo) 2012-01-08.

Revision History:

--*/
#ifndef NLSAT_ASSIGNMENT_H_
#define NLSAT_ASSIGNMENT_H_

#include "nlsat/nlsat_types.h"
#include "math/polynomial/algebraic_numbers.h"

namespace nlsat {

    /**
       \brief A mapping from variables to values. 
       This mapping is used to encode the current partial interpretation in nlsat.
    */
    class assignment : public polynomial::var2anum {
        scoped_anum_vector m_values;
        svector<bool>      m_assigned;
    public:
        assignment(anum_manager & _m):m_values(_m) {}
        virtual ~assignment() {}
        anum_manager & am() const { return m_values.m(); }
        void swap(assignment & other) {
            m_values.swap(other.m_values);
            m_assigned.swap(other.m_assigned);
        }
        void copy(assignment const& other) {
            m_assigned.reset();
            m_assigned.append(other.m_assigned);
            m_values.reserve(m_assigned.size(), anum());
            for (unsigned i = 0; i < m_assigned.size(); ++i) {
                if (is_assigned(i)) {
                    am().set(m_values[i], other.value(i));
                }
            }
        }

        void set_core(var x, anum & v) {
            m_values.reserve(x+1, anum());
            m_assigned.reserve(x+1, false); 
            m_assigned[x] = true;
            am().swap(m_values[x], v); 
        }
        void set(var x, anum const & v) {
            m_values.reserve(x+1, anum());
            m_assigned.reserve(x+1, false); 
            m_assigned[x] = true;
            am().set(m_values[x], v); 
        }
        void reset(var x) { if (x < m_assigned.size()) m_assigned[x] = false; }
        void reset() { m_assigned.reset(); }
        bool is_assigned(var x) const { return m_assigned.get(x, false); }
        anum const & value(var x) const { return m_values[x]; }
        anum_manager & m() const override { return am(); }
        bool contains(var x) const override { return is_assigned(x); }
        anum const & operator()(var x) const override { SASSERT(is_assigned(x)); return value(x); }
        void swap(var x, var y) {
            SASSERT(x < m_values.size() && y < m_values.size());
            std::swap(m_assigned[x], m_assigned[y]);
            std::swap(m_values[x], m_values[y]);
        }
        void display(std::ostream& out) const {
            for (unsigned i = 0; i < m_assigned.size(); ++i) {
                if (m_assigned[i]) {
                    out << "x" << i << " := ";
                    m_values.m().display(out, m_values[i]);
                    out << "\n";
                }
            }
        }
    };
    
    /**
       \brief Wrapper for temporarily unassigning a given variable y.
       That is, given an assignment M, M' = undef_var_assignment(M, y) is identical
       to M, but y is unassigned in M'
    */
    class undef_var_assignment : public polynomial::var2anum {
        assignment const & m_assignment;
        var                m_y;
    public:
        undef_var_assignment(assignment const & a, var y):m_assignment(a), m_y(y) {}
        anum_manager & m() const override { return m_assignment.am(); }
        bool contains(var x) const override { return x != m_y && m_assignment.is_assigned(x); }
        anum const & operator()(var x) const override { return m_assignment.value(x); }
    };
};

#endif
