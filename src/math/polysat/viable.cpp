/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    maintain viable domains

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/

#include "math/polysat/viable.h"
#include "math/polysat/solver.h"
#include "math/interval/mod_interval_def.h"


namespace polysat {

#if NEW_VIABLE

    dd::find_t viable_set::find_hint(rational const& d, rational& val) const {
        if (is_empty())
            return dd::find_t::empty;
        // 
        // ignore d since with a single interval, 
        // backtracking does not ensure that non-boundary bounds are removed.
        // viable_set could have multiple intervals to support arbitrary partitions
        // this is similar to interval_set or might even be an instance of it.
        // 
        val = lo;
        if (lo + 1 == hi || hi == 0 && is_max(lo))
            return dd::find_t::singleton;
        return dd::find_t::multiple;
    }

    bool viable_set::is_max(rational const& a) const {
        return a + 1 == rational::power_of_two(m_num_bits);
    }
    
    bool viable_set::is_singleton(rational& val) const {
        return !is_empty() && (lo + 1 == hi || (hi == 0 && is_max(lo)));
    }

    void viable_set::intersect_eq(rational const& a, bool is_positive) {
        if (is_empty())
            return;
        if (is_positive) {
            if (!contains(a))
                set_empty();
            else if (is_max(a))
                lo = a, hi = 0;
            else
                lo = a, hi = a + 1;
        }
        else {
            if (!contains(a))
                return;
            if (a == lo && a + 1 == hi)
                set_empty();
            if (a == lo && hi == 0 && is_max(a))
                set_empty();
            else if (a == lo)
                lo = a + 1;
            else if (a + 1 == hi)
                hi = a;
            else if (hi == 0 && is_max(a))
                hi = a;
            else 
                std::cout << "diseq " << lo << " " << a << " " << hi << "\n";
        }
    }

    void viable_set::intersect_eq(rational const& a, rational const& b, bool is_positive) {
        if (a.is_odd()) {
            if (b == 0)
                intersect_eq(b, is_positive);
            else {
                rational a_inv;
                VERIFY(a.mult_inverse(m_num_bits, a_inv));
                intersect_eq(mod(a_inv * -b, rational::power_of_two(m_num_bits)), is_positive);
            }
        }
    }

    void viable_set::intersect_ule(rational const& a, rational const& b, rational const& c, rational const& d, bool is_positive) {
        // x <= 0
        if (a == 1 && b == 0 && c == 0 && d == 0) 
            intersect_eq(b, is_positive);
        else if (a == 1 && b == 0 && c == 0) {
            // x <= d
            if (is_positive) 
                set_hi(d);
            // x > d
            else if (is_max(d))
                set_empty();
            else
                set_lo(d + 1);
        }
        else if (a == 0 && c == 1 && d == 0) {
            // x >= b
            if (is_positive) 
                set_lo(b);
            else if (b == 0)
                set_empty();
            else 
                set_hi(b - 1);
        }            
    }

    void viable_set::set_hi(rational const& d) {
        if (is_max(d))
            return;
        else if (is_free())
            lo = 0, hi = d + 1;
        else if (lo > d)
            set_empty();
        else if (hi != 0 || d + 1 < hi)
            hi = d + 1;       
        else 
            std::cout << "set hi " << lo << " " << d << " " << hi << "\n";
    }

    void viable_set::set_lo(rational const& b) {
        if (hi != 0 && hi <= b)
            set_empty();
        else if (is_free())
            lo = b, hi = 0;
        else if (lo < b)
            lo = b;                    
        else 
            std::cout << "set lo " << lo << " " << b << " " << hi << "\n";
    }
#endif

    viable::viable(solver& s):
        s(s)
#if !NEW_VIABLE
        ,
        m_bdd(1000)
#endif
    {}

    void viable::push_viable(pvar v) {
        s.m_trail.push_back(trail_instr_t::viable_i);
        m_viable_trail.push_back(std::make_pair(v, m_viable[v]));
    }

    void viable::pop_viable() {
        auto p = m_viable_trail.back();
        m_viable[p.first] = p.second;
        m_viable_trail.pop_back();
    }


    // a*v + b == 0 or a*v + b != 0
    void viable::intersect_eq(rational const& a, pvar v, rational const& b, bool is_positive) {
#if NEW_VIABLE
        push_viable(v);
        m_viable[v].intersect_eq(a, b, is_positive);
        if (m_viable[v].is_empty())
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
        m_viable[v].intersect_ule(a, b, c, d, is_positive);
        if (m_viable[v].is_empty())
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

    bool viable::has_viable(pvar v) {
#if NEW_VIABLE
        return !m_viable[v].is_empty();
#else
        return !m_viable[v].is_false();
#endif
    }

    bool viable::is_viable(pvar v, rational const& val) {
#if NEW_VIABLE
        return m_viable[v].contains(val);
#else
        return var2bits(v).contains(m_viable[v], val);
#endif
    }

    void viable::add_non_viable(pvar v, rational const& val) {
#if NEW_VIABLE
        push_viable(v);
        m_viable[v].set_ne(val);
        if (m_viable[v].is_empty())
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
        return m_viable[v].find_hint(s.m_value[v], val);
#else
        return var2bits(v).find_hint(m_viable[v], s.m_value[v], val);
#endif
    }

#if !NEW_VIABLE
    dd::fdd const& viable::sz2bits(unsigned sz) {
        m_bits.reserve(sz + 1);
        auto* bits = m_bits[sz];
        if (!bits) {
            m_bits.set(sz, alloc(dd::fdd, m_bdd, sz));
            bits = m_bits[sz];
        }
        return *bits;
    }
#endif

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
                            
            LOG("Viable for pvar " << v << ": " << xs);
        } 
        else {
            LOG("Viable for pvar " << v << ": <range too big>");
        }
    }
#endif

#if !NEW_VIABLE
    dd::fdd const& viable::var2bits(pvar v) { return sz2bits(s.size(v)); }
#endif


}

