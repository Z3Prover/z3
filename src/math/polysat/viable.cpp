
#include "math/polysat/viable.h"
#include "math/polysat/solver.h"

namespace polysat {

    viable::viable(solver& s):
        s(s),
        m_bdd(1000)
    {}

    void viable::push_viable(pvar v) {
        s.m_trail.push_back(trail_instr_t::viable_i);
        m_viable_trail.push_back(std::make_pair(v, m_viable[v]));
    }

    void viable::pop_viable() {
        auto p = m_viable_trail.back();
        LOG_V("Undo viable_i");
        m_viable[p.first] = p.second;
        m_viable_trail.pop_back();
    }

    // a*v + b == 0 or a*v + b != 0
    void viable::intersect_eq(rational const& a, pvar v, rational const& b, bool is_positive) {
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
    }

    bool viable::has_viable(pvar v) {
        return !m_viable[v].is_false();
    }

    bool viable::is_viable(pvar v, rational const& val) {
        return var2bits(v).contains(m_viable[v], val);
    }

    void viable::add_non_viable(pvar v, rational const& val) {
        LOG("pvar " << v << " /= " << val);
        SASSERT(is_viable(v, val));
        auto const& bits = var2bits(v);
        intersect_viable(v, bits.var() != val);
    }

    void viable::intersect_viable(pvar v, bdd vals) {
        push_viable(v);
        m_viable[v] &= vals;
        if (m_viable[v].is_false())
            s.set_conflict(v);
    }

    dd::find_t viable::find_viable(pvar v, rational & val) {
        return var2bits(v).find_hint(m_viable[v], s.m_value[v], val);
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
        if (m_viable.size() < 10) {
            for (pvar v = 0; v < m_viable.size(); ++v) {
                log(v);
            }
        }
    }

    void viable::log(pvar v) {
        if (s.size(v) <= 5) {
            vector<rational> xs;
            for (rational x = rational::zero(); x < rational::power_of_two(s.size(v)); x += 1) {
                if (is_viable(v, x)) {
                    xs.push_back(x);
                }
            }
            LOG("Viable for pvar " << v << ": " << xs);
        } else {
            LOG("Viable for pvar " << v << ": <range too big>");
        }
    }
#endif

    dd::fdd const& viable::var2bits(pvar v) { return sz2bits(s.size(v)); }


}

