/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_types.cpp

Abstract:

    Basic types used in the nonlinear arithmetic satisfiability procedure.

Author:

    Leonardo de Moura (leonardo) 2012-01-02.

Revision History:

--*/
#include "nlsat/nlsat_types.h"
#include "util/debug.h"
#include "util/hash.h"
#include "math/polynomial/polynomial.h"
 
namespace nlsat {

    ineq_atom::ineq_atom(kind k, unsigned sz, poly * const * ps, bool const * is_even, var max_var):
        atom(k, max_var),
        m_size(sz) {
        for (unsigned i = 0; i < m_size; i++) {
            m_ps[i] = TAG(poly *, ps[i], is_even[i] ? 1 : 0);
        }
        SASSERT(is_ineq_atom());
    }

    unsigned ineq_atom::hash_proc::operator()(ineq_atom const * a) const {
        return get_composite_hash<ineq_atom const *, ineq_atom::khasher, ineq_atom::chasher>(a, a->m_size);
    }

    bool ineq_atom::eq_proc::operator()(ineq_atom const * a1, ineq_atom const * a2) const {
        if (a1->m_size != a2->m_size || a1->m_kind != a2->m_kind)
            return false;
        unsigned sz = a1->m_size;
        for (unsigned i = 0; i < sz; i++) {
            if (a1->m_ps[i] != a2->m_ps[i])
                return false;
        }
        return true;
    }

    root_atom::root_atom(kind k, var x, unsigned i, poly * p):
        atom(k, x),
        m_x(x),
        m_i(i),
        m_p(p) {
        SASSERT(is_root_atom());
    }

    unsigned root_atom::hash_proc::operator()(root_atom const * a) const {
        unsigned _a = a->m_x;
        unsigned _b = ((a->m_i << 2) | (a->m_kind));
        unsigned _c = polynomial::manager::id(a->m_p);
        mix(_a, _b, _c);
        return _c;
    }

    bool root_atom::eq_proc::operator()(root_atom const * a1, root_atom const * a2) const {
        return a1->m_kind == a2->m_kind && a1->m_x == a2->m_x && a1->m_i == a2->m_i && a1->m_p == a2->m_p;
    }

};
