/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    maintain viable domains

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

Notes:

TODO: Investigate in depth a notion of phase caching for variables.
The Linear solver can be used to supply a phase in some cases.
In other cases, the phase of a variable assignment across branches
might be used in a call to is_viable. With phase caching on, it may
just check if the cached phase is viable without detecting that it is a propagation.

--*/


#include "util/debug.h"
#include "math/polysat/viable.h"
#include "math/polysat/solver.h"

namespace polysat {

    viable::viable(solver& s) : s(s) {}

    viable::~viable() {
        for (entry* e : m_alloc) 
            dealloc(e);        
    }

    viable::entry* viable::alloc_entry() {
        rational coeff(1);
        if (m_alloc.empty())
            return alloc(entry, coeff);
        auto* e = m_alloc.back();
        e->side_cond.reset();
        e->coeff = coeff;
        m_alloc.pop_back();
        return e;
    }

    void viable::pop_viable() {
        auto& [v, is_unit, e] = m_trail.back();
        auto& vec = is_unit ? m_units[v] : m_non_units[v];
        e->remove_from(vec, e);
        m_alloc.push_back(e);       
        m_trail.pop_back();
    }

    void viable::push_viable() {
        auto& [v, is_unit, e] = m_trail.back();
        SASSERT(e->prev() != e || !m_units[v]);
        SASSERT(e->prev() != e || e->next() == e);
        SASSERT(is_unit);
        (void)is_unit;
        if (e->prev() != e) {
            e->prev()->insert_after(e);
            if (e->interval.lo_val() < e->next()->interval.lo_val())
                m_units[v] = e;
        }
        else 
            m_units[v] = e;        
        m_trail.pop_back();
    }

    bool viable::intersect(pvar v, signed_constraint const& c) {
        auto& fi = s.m_forbidden_intervals;
        entry* ne = alloc_entry();
        if (!fi.get_interval(c, v, ne->coeff, ne->interval, ne->side_cond) || ne->interval.is_currently_empty()) {
            m_alloc.push_back(ne);
            return false;
        }
        else if (ne->coeff == 1) {
            ne->src = c;
            return intersect(v, ne);
        }
        else {
            ne->src = c;
            m_trail.push_back({ v, false, ne });
            s.m_trail.push_back(trail_instr_t::viable_add_i);
            ne->init(ne);
            if (!m_non_units[v])
                m_non_units[v] = ne;
            else
                ne->insert_after(m_non_units[v]);
            return true;
        }
    }

    bool viable::intersect(pvar v, entry* ne) {
        entry* e = m_units[v];
        if (e && e->interval.is_full()) {
            m_alloc.push_back(ne);
            return false;
        }

        if (ne->interval.is_currently_empty()) {
            m_alloc.push_back(ne);
            return false;
        }

        auto create_entry = [&]() {
            m_trail.push_back({ v, true, ne });
            s.m_trail.push_back(trail_instr_t::viable_add_i);
            ne->init(ne);            
            return ne;
        };

        auto remove_entry = [&](entry* e) {
            m_trail.push_back({ v, true, e });
            s.m_trail.push_back(trail_instr_t::viable_rem_i);
            e->remove_from(m_units[v], e);
        };

        if (!e) 
            m_units[v] = create_entry();
        else {
            entry* first = e;
            do {
                if (e->interval.contains(ne->interval)) {
                    m_alloc.push_back(ne);
                    return false;
                }
                while (ne->interval.contains(e->interval)) {
                    entry* n = e->next();
                    remove_entry(e);
                    if (!m_units[v]) {
                        m_units[v] = create_entry();
                        return true;
                    }
                    if (e == first) 
                        first = n;                    
                    e = n;
                }             
                SASSERT(e->interval.lo_val() != ne->interval.lo_val());
                if (e->interval.lo_val() > ne->interval.lo_val()) {
                    if (first->prev()->interval.contains(ne->interval)) {
                        m_alloc.push_back(ne);
                        return false;
                    }
                    e->insert_before(create_entry());
                    if (e == first)
                        m_units[v] = e->prev();
                    SASSERT(well_formed(m_units[v]));
                    return true;
                }
                e = e->next();
            }             
            while (e != first);
            // otherwise, append to end of list
            first->insert_before(create_entry());
        }
        SASSERT(well_formed(m_units[v]));
        return true;
    }

    /**
    * Traverse all interval constraints with coefficients to check whether current value 'val' for
    * 'v' is feasible. If not, extract a (maximal) interval to block 'v' from being assigned val.
    * 
    * To investigate:
    * - side conditions are stronger than for unit intervals. They constrain the lower and upper bounds to
    *   be precisely the assigned values. This is to ensure that lo/hi that are computed based on lo_val 
    *   and division with coeff are valid. Is there a more relaxed scheme?
    */
    bool viable::refine_viable(pvar v, rational const& val) {
        auto* e = m_non_units[v];
        if (!e)
            return true;
        entry* first = e;
        rational const& max_value = s.var2pdd(v).max_value();
        do {
            rational coeff_val = mod(e->coeff * val, max_value + 1);
            if (e->interval.currently_contains(coeff_val)) {
                rational delta_l = floor((coeff_val - e->interval.lo_val()) / e->coeff);
                rational delta_u = floor((e->interval.hi_val() - coeff_val - 1) / e->coeff);
                rational lo = val - delta_l;
                rational hi = val + delta_u + 1;

                if (e->interval.lo_val() < e->interval.hi_val()) {
                    // pass
                }
                else if (e->interval.lo_val() <= coeff_val) {
                    rational lambda_u = floor((max_value - coeff_val - 1) / e->coeff);
                    hi = val + lambda_u + 1;
                    if (hi > max_value)
                        hi = 0;
                }
                else {
                    SASSERT(coeff_val < e->interval.hi_val());
                    rational lambda_l = floor(coeff_val / e->coeff);
                    lo = val - lambda_l;                   
                }
                SASSERT(hi <= s.var2pdd(v).max_value());
                LOG("forbidden interval " << e->interval << " [" << lo << ", " << hi << "[");
                entry* ne = alloc_entry();
                ne->src = e->src;
                ne->side_cond = e->side_cond;
                ne->side_cond.push_back(s.eq(e->interval.hi(), e->interval.hi_val()));
                ne->side_cond.push_back(s.eq(e->interval.lo(), e->interval.lo_val()));
                ne->coeff = 1;
                pdd lop = s.var2pdd(v).mk_val(lo);
                pdd hip = s.var2pdd(v).mk_val(hi);
                ne->interval = eval_interval::proper(lop, lo, hip, hi);
                intersect(v, ne);
                return false;
            }
            e = e->next();
        }         
        while (e != first);
        return true;
    }

    bool viable::has_viable(pvar v) {     
        refined:
        auto* e = m_units[v];

#define CHECK_RETURN(val) { if (refine_viable(v, val)) return true; else goto refined; }

        if (!e)
            CHECK_RETURN(rational::zero());
        entry* first = e;
        entry* last = e->prev();

        // quick check: last interval doesn't wrap around, so hi_val
        // has not been covered
        if (last->interval.lo_val() < last->interval.hi_val()) 
            CHECK_RETURN(last->interval.hi_val());
        
        do {
            if (e->interval.is_full())
                return false;
            entry* n = e->next();
            if (n == e)
                CHECK_RETURN(e->interval.hi_val());
            if (!n->interval.currently_contains(e->interval.hi_val()))
                CHECK_RETURN(e->interval.hi_val());
            if (n == first) {
                if (e->interval.lo_val() > e->interval.hi_val())
                    return false;
                CHECK_RETURN(e->interval.hi_val());              
            }
            e = n;
        }         
        while (e != first);
        return false;
    }

    bool viable::is_viable(pvar v, rational const& val) { 
        auto* e = m_units[v];
        if (!e)
            return refine_viable(v, val);
        entry* first = e;
        entry* last = first->prev();
        if (last->interval.currently_contains(val))
            return false;
        for (; e != last; e = e->next()) {        
            if (e->interval.currently_contains(val))
                return false;
            if (val < e->interval.lo_val()) 
                return refine_viable(v, val);            
        }         
        return refine_viable(v, val);
    }

    rational viable::min_viable(pvar v) { 
        refined:
        rational lo(0);
        auto* e = m_units[v];
        if (!e && !refine_viable(v, lo))
            goto refined;
        if (!e)
            return lo;
        entry* first = e;
        entry* last = first->prev();
        if (last->interval.currently_contains(lo))
            lo = last->interval.hi_val();
        do {        
            if (!e->interval.currently_contains(lo))
                break;
            lo = e->interval.hi_val();
            e = e->next();
        }         
        while (e != first);
        if (!refine_viable(v, lo))
            goto refined;
        SASSERT(is_viable(v, lo));  
        return lo;
    }

    rational viable::max_viable(pvar v) { 
        refined:
        rational hi = s.var2pdd(v).max_value();
        auto* e = m_units[v];
        if (!e && !refine_viable(v, hi))
            goto refined;
        if (!e)
            return hi;
        entry* last = e->prev();
        e = last;
        do {
            if (!e->interval.currently_contains(hi))
                break;
            hi = e->interval.lo_val() - 1;
            e = e->prev();
        }           
        while (e != last);
        if (!refine_viable(v, hi))
            goto refined;
        SASSERT(is_viable(v, hi));
        return hi;
    }

    dd::find_t viable::find_viable(pvar v, rational& lo) { 
        refined:
        lo = 0;
        auto* e = m_units[v];
        if (!e && !refine_viable(v, lo))
            goto refined;
        if (!e && !refine_viable(v, rational::one()))
            goto refined;
        if (!e)
            return dd::find_t::multiple;
        if (e->interval.is_full())
            return dd::find_t::empty;

        entry* first = e;
        entry* last = first->prev();

        // quick check: last interval does not wrap around
        // and has space for 2 unassigned values.
        auto& max_value = s.var2pdd(v).max_value();
        if (last->interval.lo_val() < last->interval.hi_val() &&
            last->interval.hi_val() < max_value) {
            lo = last->interval.hi_val();
            if (!refine_viable(v, lo))
                goto refined;
            if (!refine_viable(v, max_value))
                goto refined;
            return dd::find_t::multiple;
        }

        // find lower bound
        if (last->interval.currently_contains(lo))
            lo = last->interval.hi_val();
        do {
            if (!e->interval.currently_contains(lo))
                break;
            lo = e->interval.hi_val();
            e = e->next();
        }         
        while (e != first);

        if (e->interval.currently_contains(lo))
            return dd::find_t::empty;

        // find upper bound
        rational hi = max_value;
        e = last;
        do {
            if (!e->interval.currently_contains(hi))
                break;
            hi = e->interval.lo_val() - 1;
            e = e->prev();
        }         
        while (e != last);
        if (!refine_viable(v, lo))
            goto refined;
        if (!refine_viable(v, hi))
            goto refined;
        if (lo == hi)
            return dd::find_t::singleton;
        else
            return dd::find_t::multiple;
    }

    bool viable::resolve(pvar v, conflict& core) {
        if (has_viable(v))
            return false;
        auto* e = m_units[v];
        entry* first = e;
        SASSERT(e);
        core.reset();
        do {
            // Build constraint: upper bound of each interval is not contained in the next interval,
            // using the equivalence:  t \in [l;h[  <=>  t-l < h-l
            entry* n = e->next();
            if (!e->interval.is_full()) {
                auto const& hi = e->interval.hi();
                auto const& next_lo = n->interval.lo();
                auto const& next_hi = n->interval.hi();
                auto lhs = hi - next_lo;
                auto rhs = next_hi - next_lo;
                signed_constraint c = s.m_constraints.ult(lhs, rhs);
                core.insert(c);
            }
            for (auto sc : e->side_cond)
                core.insert(sc);
            e->src->set_var_dependent(); 
            core.insert(e->src);
            e = n;
        }             
        while (e != first);

        core.set_bailout();
        for (auto c : core) {
            if (c.bvalue(s) == l_false) {
                core.reset();
                core.set(~c);
                break;
            }
        }
        return true;
    }

    void viable::log(pvar v) {
        if (!well_formed(m_units[v]))
            LOG("v" << v << " not well formed");
        auto* e = m_units[v];
        if (!e)
            return;
        entry* first = e;
        do {
            LOG("v" << v << ": " << e->interval << " " << e->side_cond << " " << e->src);
            e = e->next();
        }         
        while (e != first);
    }

    void viable::log() {
        for (pvar v = 0; v < std::min(10u, m_units.size()); ++v)
            log(v);
    }

    std::ostream& viable::display(std::ostream& out, pvar v, entry* e) const {
        if (!e)
            return out;
        entry* first = e;
        do {
            if (e->coeff != 1)
                out << e->coeff << " * v" << v << " ";
            out << e->interval << " " << e->side_cond << " " << e->src << "; ";
            e = e->next();
        }         
        while (e != first);
        return out;
    }

    std::ostream& viable::display(std::ostream& out, pvar v) const {
        display(out, v, m_units[v]);
        display(out, v, m_non_units[v]);
        return out;
    }

    std::ostream& viable::display(std::ostream& out) const {
        for (pvar v = 0; v < m_units.size(); ++v)
            display(out << "v" << v << ": ", v);
        return out;
    }

    /*
    * Lower bounds are strictly ascending.
    * intervals don't contain each-other (since lower bounds are ascending, 
    * it suffices to check containment in one direction).
    */
    bool viable::well_formed(entry* e) {
        if (!e)
            return true;
        entry* first = e;
        while (true) {
            if (e->interval.is_full())
                return e->next() == e;
            if (e->interval.is_currently_empty()) 
                return false;
            
            auto* n = e->next();
            if (n != e && e->interval.contains(n->interval)) 
                return false;
            
            if (n == first)
                break;            
            if (e->interval.lo_val() >= n->interval.lo_val())
                return false;
            e = n;
        }
        return true;
    }


}

