/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_scoped_literal_vector.h

Abstract:

    Scoped vector for nlsat literals.
    Just to be "cancel" safe.

Author:

    Leonardo de Moura (leonardo) 2012-01-13.

Revision History:

--*/
#ifndef NLSAT_SCOPED_LITERAL_VECTOR_H_
#define NLSAT_SCOPED_LITERAL_VECTOR_H_

#include "nlsat/nlsat_solver.h"

namespace nlsat {

    class scoped_literal_vector {
        solver &       m_solver;
        literal_vector m_lits;
    public:
        scoped_literal_vector(solver & s):m_solver(s) {}
        ~scoped_literal_vector() { reset(); }
        unsigned size() const { return m_lits.size(); }
        bool empty() const { return m_lits.empty(); }
        literal operator[](unsigned i) const { return m_lits[i]; }
        void reset() {
            unsigned sz = m_lits.size();
            for (unsigned i = 0; i < sz; i++) {
                m_solver.dec_ref(m_lits[i]);
            }
            m_lits.reset();
        }
        void push_back(literal l) {
            m_solver.inc_ref(l);
            m_lits.push_back(l);
        }
        void set(unsigned i, literal l) {
            m_solver.inc_ref(l);
            m_solver.dec_ref(m_lits[i]);
            m_lits[i] = l;
        }
        literal const * c_ptr() const { return m_lits.c_ptr(); }
        void shrink(unsigned new_sz) {
            SASSERT(new_sz <= m_lits.size());
            unsigned sz = m_lits.size();
            if (new_sz == sz)
                return;
            for (unsigned i = new_sz; i < sz; i++) {
                m_solver.dec_ref(m_lits[i]);
            }
            m_lits.shrink(new_sz);
        }
        void append(unsigned sz, literal const * ls) {
            for (unsigned i = 0; i < sz; i++)
                push_back(ls[i]);
        }
        void append(scoped_literal_vector const& ls) {
            append(ls.size(), ls.c_ptr());
        }
        void swap(scoped_literal_vector& other) {
            SASSERT(&m_solver == &other.m_solver);
            m_lits.swap(other.m_lits);
        }
    };


    class scoped_literal {
        solver &  m_solver;
        literal   m_lit;
    public:
        scoped_literal(solver & s):m_solver(s), m_lit(null_literal) {}
        ~scoped_literal() { m_solver.dec_ref(m_lit); }
        scoped_literal & operator=(literal l) { 
            m_solver.inc_ref(l);
            m_solver.dec_ref(m_lit);
            m_lit = l;
            return *this;
        }
        scoped_literal & operator=(scoped_literal const & l) { return operator=(l.m_lit); }
        operator literal&() { return m_lit; }
        operator literal const &() const { return m_lit; }
        void neg() { m_lit.neg(); }
    };
};

#endif
