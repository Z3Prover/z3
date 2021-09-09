/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    maintain viable domains

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

Notes:

Use cheap heuristics to narrow viable sets whenever possible.
If the cheap heuristics fail, compute a BDD representing the viable sets
and narrow the range using the BDDs that are cached.


--*/


#include "math/polysat/viable.h"
#include "math/polysat/solver.h"
#if NEW_VIABLE
#include "math/polysat/viable_set_def.h"
#endif


namespace polysat {


    viable::viable(solver& s):
        s(s),
        m_bdd(1000)
    {}

    viable::~viable() {
#if NEW_VIABLE
        ptr_vector<cached_constraint> entries;
        for (auto* e : m_constraint_cache) 
            entries.push_back(e);
        m_constraint_cache.reset();
        for (auto* e : entries)
            dealloc(e);
#endif
    }

    void viable::push_viable(pvar v) {
        s.m_trail.push_back(trail_instr_t::viable_i);
#if NEW_VIALBLE
        m_viable_trail.push_back(std::make_pair(v, alloc(viable_set, *m_viable[v])));
#else
        m_viable_trail.push_back(std::make_pair(v, m_viable[v]));
#endif

    }

    void viable::pop_viable() {
        auto p = m_viable_trail.back();
        m_viable.set(p.first, p.second);
        m_viable_trail.pop_back();
    }


    // a*v + b == 0 or a*v + b != 0
    void viable::intersect_eq(rational const& a, pvar v, rational const& b, bool is_positive) {
#if NEW_VIABLE
        push_viable(v);
        if (!m_viable[v]->intersect_eq(a, b, is_positive)) 
            intersect_eq_bdd(v, a, b, is_positive);
        if (m_viable[v]->is_empty())
            s.set_conflict(v);
#else
        
        bddv const& x = var2bits(v).var();
        if (b == 0 && a.is_odd()) {
            // hacky test optimizing special case.
            // general case is compute inverse(a)*-b for equality 2^k*a*x + b == 0
            // then constrain x.
            // 
            intersect_viable(v, is_positive ? x.all0() : !x.all0());
        }
        else if (a.is_odd()) {
            rational a_inv;
            VERIFY(a.mult_inverse(x.size(), a_inv));
            bdd eq = x == mod(a_inv * -b, rational::power_of_two(x.size()));
            intersect_viable(v, is_positive ? eq : !eq);
        }
        else {
            IF_VERBOSE(10, verbose_stream() << a << "*x + " << b << "\n");
            
            bddv lhs = a * x + b;
            bdd xs = is_positive ? lhs.all0() : !lhs.all0();
            intersect_viable(v, xs);
        }
#endif
    }

    void viable::intersect_ule(pvar v, rational const& a, rational const& b, rational const& c, rational const& d, bool is_positive) {
#if NEW_VIABLE
        push_viable(v);
        if (!m_viable[v]->intersect_le(a, b, c, d, is_positive)) 
            intersect_ule_bdd(v, a, b, c, d, is_positive);
        if (m_viable[v]->is_empty())
            s.set_conflict(v);
#else
        bddv const& x = var2bits(v).var();
        // hacky special case
        if (a == 1 && b == 0 && c == 0 && d == 0) 
            // x <= 0
            intersect_viable(v, is_positive ? x.all0() : !x.all0());
        else {
            IF_VERBOSE(10, verbose_stream() << a << "*x + " << b << (is_positive ? " <= " : " > ") << c << "*x + " << d << "\n");
            bddv l = a * x + b;
            bddv r = c * x + d;
            bdd xs = is_positive ? (l <= r) : (l > r);
            intersect_viable(v, xs);
        }
#endif
    }

#if NEW_VIABLE

    viable::cached_constraint& viable::cache_constraint(pvar v, cached_constraint& entry0, std::function<bdd(void)>& mk_constraint) {        
        cached_constraint* other = nullptr;
        if (!m_constraint_cache.find(&entry0, other)) {
            gc_cached_constraints();
            other = alloc(cached_constraint, entry0);
            other->repr = mk_constraint();
            m_constraint_cache.insert(other);
        }
        other->m_activity++;
        return *other;
    }

    void viable::gc_cached_constraints() {
        // 
        // TODO: instead of using activity for GC, use the Move-To-Front approach 
        // see sat/smt/bv_ackerman.h or sat/smt/euf_ackerman.h
        // where hash table entries use a dll_base.
        // 
        unsigned max_entries = 10000;
        if (m_constraint_cache.size() > max_entries) {
            ptr_vector<cached_constraint> entries;
            for (auto* e : m_constraint_cache) 
                entries.push_back(e);
            std::stable_sort(entries.begin(), entries.end(), [&](cached_constraint* a, cached_constraint* b) { return a->m_activity < b->m_activity; });
	    for (auto* e : entries)
		e->m_activity /= 2;
            for (unsigned i = 0; i < max_entries/2; ++i) {
                m_constraint_cache.remove(entries[i]);
                dealloc(entries[i]);
            }
        }
    }

    void viable::narrow(pvar v, bdd const& is_false) {        
        rational bound = m_viable[v]->lo;
        if (var2bits(v).sup(is_false, bound)) 
            m_viable[v]->update_lo(m_viable[v]->next(bound));
        bound = m_viable[v]->prev(m_viable[v]->hi);
        if (var2bits(v).inf(is_false, bound)) 
            m_viable[v]->update_hi(m_viable[v]->prev(bound));	
    }

    void viable::intersect_ule_bdd(pvar v, rational const& a, rational const& b, rational const& c, rational const& d, bool is_positive) {
        unsigned sz = var2bits(v).num_bits();
        std::function<bdd(void)> le = [&]() {
            bddv const& x = var2bits(v).var();
            return ((a * x) + b) <= ((c * x) + d);
        };
        cached_constraint entry0(sz, a, b, c, d, m_bdd.mk_true());
        cached_constraint& entry = cache_constraint(v, entry0, le);

        // le(lo) is false: find min x >= lo, such that le(x) is false, le(x+1) is true
        // le(hi) is false: find max x =< hi, such that le(x) is false, le(x-1) is true
        bdd gt = is_positive ? !entry.repr : entry.repr;
        narrow(v, gt);        
    }

    void viable::intersect_eq_bdd(pvar v, rational const& a, rational const& b, bool is_positive) {
        unsigned sz = var2bits(v).num_bits();
        std::function<bdd(void)> eq = [&]() {
            bddv const& x = var2bits(v).var();
            return ((a * x) + b) == rational(0);
        };
        cached_constraint entry0(sz, a, b, m_bdd.mk_true());
        cached_constraint& entry = cache_constraint(v, entry0, eq);

        bdd ne = is_positive ? !entry.repr : entry.repr;
        narrow(v, ne);        
    }
#endif

    bool viable::has_viable(pvar v) {
#if NEW_VIABLE
        return !m_viable[v]->is_empty();
#else
        return !m_viable[v].is_false();
#endif
    }

    bool viable::is_viable(pvar v, rational const& val) {
#if NEW_VIABLE
        return m_viable[v]->contains(val);
#else
        return var2bits(v).contains(m_viable[v], val);
#endif
    }

    void viable::add_non_viable(pvar v, rational const& val) {
#if NEW_VIABLE
        push_viable(v);
        IF_VERBOSE(10, verbose_stream() << " v" << v << " != " << val << "\n");
        m_viable[v]->intersect_diff(val);
        if (m_viable[v]->is_empty())
            s.set_conflict(v);
#else
        LOG("pvar " << v << " /= " << val);
        SASSERT(is_viable(v, val));
        auto const& bits = var2bits(v);
        intersect_viable(v, bits.var() != val);
#endif
    }

#if !NEW_VIABLE
    void viable::intersect_viable(pvar v, bdd vals) {
        push_viable(v);
        m_viable[v] &= vals;
        if (m_viable[v].is_false())
            s.set_conflict(v);
    }
#endif

    dd::find_t viable::find_viable(pvar v, rational & val) {
#if NEW_VIABLE
        return m_viable[v]->find_hint(s.m_value[v], val);
#else
        return var2bits(v).find_hint(m_viable[v], s.m_value[v], val);
#endif
    }

    rational viable::min_viable(pvar v) {
        return var2bits(v).min(m_viable[v]);
    }

    rational viable::max_viable(pvar v) {
        return var2bits(v).max(m_viable[v]);
    }

    dd::fdd const& viable::sz2bits(unsigned sz) {
        m_bits.reserve(sz + 1);
        auto* bits = m_bits[sz];
        if (!bits) {
            m_bits.set(sz, alloc(dd::fdd, m_bdd, sz));
            bits = m_bits[sz];
        }
        return *bits;
    }

#if POLYSAT_LOGGING_ENABLED
    void viable::log() {
        // only for small problems
        for (pvar v = 0; v < std::min(10u, m_viable.size()); ++v) 
            log(v);            
    }

    void viable::log(pvar v) {
        if (s.size(v) <= 5) {
            vector<rational> xs;
            for (rational x = rational::zero(); x < rational::power_of_two(s.size(v)); x += 1) 
                if (is_viable(v, x)) 
                    xs.push_back(x);
                            
            LOG("Viable for v" << v << ": " << xs);
        } 
    }
#endif

    dd::fdd const& viable::var2bits(pvar v) { return sz2bits(s.size(v)); }


}

