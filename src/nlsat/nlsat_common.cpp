/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_common.cpp

Abstract:

    some common routines from nlsat

Author:

    Lev Nachmanson(levnach@hotmail.com) 2025-October.

Revision History:

--*/
#include "nlsat/nlsat_common.h"
namespace nlsat {

    todo_set::todo_set(polynomial::cache& u, bool canonicalize): m_cache(u), m_set(u.pm()), m_canonicalize(canonicalize) {}

    void todo_set::reset() {
        pmanager& pm = m_set.m();
        unsigned sz = m_set.size();
        for (unsigned i = 0; i < sz; i++) {
            m_in_set[pm.id(m_set.get(i))] = false;
        }
        m_set.reset();
    }

    poly* todo_set::insert(poly* p) {
        pmanager& pm = m_set.m();
        if (m_in_set.get(pm.id(p), false))
            return p;
        if (m_cache.contains(p)) {
            // still have to insert in the set
            m_in_set.setx(pm.id(p), true, false);
            m_set.push_back(p);
            return p;    
        }
        polynomial_ref pinned(pm); // keep canonicalized polynomial alive until it is stored
        if (m_canonicalize) {
            // Canonicalize content+sign so scalar multiples share the same representative.
            if (!pm.is_zero(p) && !pm.is_const(p)) {
                var x = pm.max_var(p);
                pm.primitive(p, x, pinned);
                p = pinned.get();
            }
            else
                pinned = p;
            p = pm.flip_sign_if_lm_neg(p);
            pinned = p;
        }
        p = m_cache.mk_unique(p);
        unsigned pid = pm.id(p);
        if (!m_in_set.get(pid, false)) {
            m_in_set.setx(pid, true, false);
            m_set.push_back(p);
        }
        return p;
    }

    bool todo_set::contains(poly* p) const {
        if (!p)
            return false;
        pmanager& pm = m_set.m();
        return m_in_set.get(pm.id(p), false);
    }

    bool todo_set::empty() const { return m_set.empty(); }

    // Return max variable in todo_set
    var todo_set::max_var() const {
        pmanager& pm = m_set.m();
        var max = null_var;
        unsigned sz = m_set.size();
        for (unsigned i = 0; i < sz; i++) {
            var x = pm.max_var(m_set.get(i));
            SASSERT(x != null_var);
            if (max == null_var || x > max)
                max = x;
        }
        return max;
    }

    /**
       \brief Remove the maximal polynomials from the set and store
       them in max_polys. Return the maximal variable
     */
    var todo_set::extract_max_polys(polynomial_ref_vector& max_polys) {
        max_polys.reset();
        var x = max_var();
        pmanager& pm = m_set.m();
        unsigned sz = m_set.size();
        unsigned j  = 0;
        for (unsigned i = 0; i < sz; i++) {
            poly* p = m_set.get(i);
            var y = pm.max_var(p);
            SASSERT(y <= x);
            if (y == x) {
                max_polys.push_back(p);
                m_in_set[pm.id(p)] = false;
            }
            else {
                m_set.set(j, p);
                j++;
            }
        }
        m_set.shrink(j);
        return x;
    }

    unsigned todo_set::extract_polys_at_level(var x, polynomial_ref_vector& out) {
        pmanager& pm = m_set.m();
        unsigned sz = m_set.size();
        unsigned j = 0;
        unsigned count = 0;
        for (unsigned i = 0; i < sz; i++) {
            poly* p = m_set.get(i);
            if (pm.max_var(p) == x) {
                out.push_back(p);
                m_in_set[pm.id(p)] = false;
                ++count;
            }
            else {
                m_set.set(j, p);
                j++;
            }
        }
        m_set.shrink(j);
        return count;
    }

    /**
       \brief Wrapper for factorization
    */
    void factor(polynomial_ref & p, polynomial::cache& cache, polynomial_ref_vector & fs) {
        TRACE(nlsat_factor, tout << "factor\n" << p << "\n";);
        fs.reset();
        cache.factor(p.get(), fs);
    }
}
