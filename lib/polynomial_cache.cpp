/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    polynomial_cache.cpp

Abstract:

    "Hash-consing" for polynomials

Author:

    Leonardo (leonardo) 2012-01-07

Notes:

--*/
#include"polynomial_cache.h"
#include"chashtable.h"

namespace polynomial {

    struct poly_hash_proc {
        manager & m;
        poly_hash_proc(manager & _m):m(_m) {}
        unsigned operator()(polynomial const * p) const { return m.hash(p); }
    };

    struct poly_eq_proc {
        manager & m;
        poly_eq_proc(manager & _m):m(_m) {}
        bool operator()(polynomial const * p1, polynomial const * p2) const { return m.eq(p1, p2); }
    };

    struct psc_chain_entry {
        polynomial const * m_p;
        polynomial const * m_q;
        var                m_x;
        unsigned           m_hash;
        unsigned           m_result_sz;
        polynomial **      m_result;
        
        psc_chain_entry(polynomial const * p, polynomial const * q, var x, unsigned h):
            m_p(p),
            m_q(q),
            m_x(x),
            m_hash(h),
            m_result_sz(0),
            m_result(0) {
        }
        
        struct hash_proc { unsigned operator()(psc_chain_entry const * entry) const { return entry->m_hash; } };

        struct eq_proc { 
            bool operator()(psc_chain_entry const * e1, psc_chain_entry const * e2) const {
                return e1->m_p == e2->m_p && e1->m_q == e2->m_q && e1->m_x == e2->m_x;
            }
        };
    };

    struct factor_entry {
        polynomial const * m_p;
        unsigned           m_hash;
        unsigned           m_result_sz;
        polynomial **      m_result;
        
        factor_entry(polynomial const * p, unsigned h):
            m_p(p),
            m_hash(h),
            m_result_sz(0),
            m_result(0) {
        }
        
        struct hash_proc { unsigned operator()(factor_entry const * entry) const { return entry->m_hash; } };

        struct eq_proc { 
            bool operator()(factor_entry const * e1, factor_entry const * e2) const {
                return e1->m_p == e2->m_p;
            }
        };
    };

    typedef chashtable<polynomial*, poly_hash_proc, poly_eq_proc> polynomial_table;
    typedef chashtable<psc_chain_entry*, psc_chain_entry::hash_proc, psc_chain_entry::eq_proc> psc_chain_cache;
    typedef chashtable<factor_entry*, factor_entry::hash_proc, factor_entry::eq_proc> factor_cache;
    
    struct cache::imp { 
        manager &                m;
        polynomial_table         m_poly_table;
        psc_chain_cache          m_psc_chain_cache;
        factor_cache             m_factor_cache;
        polynomial_ref_vector    m_cached_polys;
        svector<char>            m_in_cache;
        small_object_allocator & m_allocator;

        imp(manager & _m):m(_m), m_poly_table(poly_hash_proc(m), poly_eq_proc(m)), m_cached_polys(m), m_allocator(m.allocator()) {
        }
        
        ~imp() {
            reset_psc_chain_cache();
            reset_factor_cache();
        }

        void del_psc_chain_entry(psc_chain_entry * entry) {
            if (entry->m_result_sz != 0)
                m_allocator.deallocate(sizeof(polynomial*)*entry->m_result_sz, entry->m_result);
            entry->~psc_chain_entry();
            m_allocator.deallocate(sizeof(psc_chain_entry), entry);
        }

        void del_factor_entry(factor_entry * entry) {
            if (entry->m_result_sz != 0)
                m_allocator.deallocate(sizeof(polynomial*)*entry->m_result_sz, entry->m_result);
            entry->~factor_entry();
            m_allocator.deallocate(sizeof(factor_entry), entry);
        }

        void reset_psc_chain_cache() {
            psc_chain_cache::iterator it  = m_psc_chain_cache.begin();
            psc_chain_cache::iterator end = m_psc_chain_cache.end();
            for (; it != end; ++it) {
                del_psc_chain_entry(*it);
            }
            m_psc_chain_cache.reset();
        }

        void reset_factor_cache() {
            factor_cache::iterator it  = m_factor_cache.begin();
            factor_cache::iterator end = m_factor_cache.end();
            for (; it != end; ++it) {
                del_factor_entry(*it);
            }
            m_factor_cache.reset();
        }

        unsigned pid(polynomial * p) const { return m.id(p); }
        
        polynomial * mk_unique(polynomial * p) {
            if (m_in_cache.get(pid(p), false))
                return p;
            polynomial * p_prime = m_poly_table.insert_if_not_there(p);
            if (p == p_prime) {
                m_cached_polys.push_back(p_prime); 
                m_in_cache.setx(pid(p_prime), true, false);
            }
            return p_prime;
        }

        void psc_chain(polynomial * p, polynomial * q, var x, polynomial_ref_vector & S) {
            p = mk_unique(p);
            q = mk_unique(q);
            unsigned h = hash_u_u(pid(p), pid(q));
            psc_chain_entry * entry = new (m_allocator.allocate(sizeof(psc_chain_entry))) psc_chain_entry(p, q, x, h);
            psc_chain_entry * old_entry = m_psc_chain_cache.insert_if_not_there(entry); 
            if (entry != old_entry) {
                entry->~psc_chain_entry();
                m_allocator.deallocate(sizeof(psc_chain_entry), entry);
                S.reset();
                for (unsigned i = 0; i < old_entry->m_result_sz; i++) {
                    S.push_back(old_entry->m_result[i]);
                }
            }
            else {
                m.psc_chain(p, q, x, S);
                unsigned sz = S.size();
                entry->m_result_sz = sz;
                entry->m_result    = static_cast<polynomial**>(m_allocator.allocate(sizeof(polynomial*)*sz));
                for (unsigned i = 0; i < sz; i++) {
                    polynomial * h = mk_unique(S.get(i));
                    S.set(i, h);
                    entry->m_result[i] = h;
                }
            }
        }

        void factor(polynomial * p, polynomial_ref_vector & distinct_factors) {
            distinct_factors.reset();
            p = mk_unique(p);
            unsigned h = hash_u(pid(p));
            factor_entry * entry = new (m_allocator.allocate(sizeof(factor_entry))) factor_entry(p, h);
            factor_entry * old_entry = m_factor_cache.insert_if_not_there(entry); 
            if (entry != old_entry) {
                entry->~factor_entry();
                m_allocator.deallocate(sizeof(factor_entry), entry);
                distinct_factors.reset();
                for (unsigned i = 0; i < old_entry->m_result_sz; i++) {
                    distinct_factors.push_back(old_entry->m_result[i]);
                }
            }
            else {
                factors fs(m);
                m.factor(p, fs);
                unsigned sz = fs.distinct_factors();
                entry->m_result_sz = sz;
                entry->m_result    = static_cast<polynomial**>(m_allocator.allocate(sizeof(polynomial*)*sz));
                for (unsigned i = 0; i < sz; i++) {
                    polynomial * h = mk_unique(fs[i]);
                    distinct_factors.push_back(h);
                    entry->m_result[i] = h;
                }
            }
        }
    };

    cache::cache(manager & m) {
        m_imp = alloc(imp, m);
    }

    cache::~cache() {
        dealloc(m_imp);
    }
    
    manager & cache::m() const {
        return m_imp->m;
    }

    polynomial * cache::mk_unique(polynomial * p) {
        return m_imp->mk_unique(p);
    }

    void cache::psc_chain(polynomial const * p, polynomial const * q, var x, polynomial_ref_vector & S) {
        m_imp->psc_chain(const_cast<polynomial*>(p), const_cast<polynomial*>(q), x, S);
    }

    void cache::factor(polynomial const * p, polynomial_ref_vector & distinct_factors) {
        m_imp->factor(const_cast<polynomial*>(p), distinct_factors);
    }
    
    void cache::reset() {
        manager & _m = m();
        dealloc(m_imp);
        m_imp = alloc(imp, _m);
    }
};
