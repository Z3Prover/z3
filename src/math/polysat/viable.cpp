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
        if (m_alloc.empty())
            return alloc(entry);
        auto* e = m_alloc.back();
        e->side_cond.reset();
        m_alloc.pop_back();
        return e;
    }

    void viable::pop_viable() {
        auto& [v, e] = m_trail.back();
        e->remove_from(m_viable[v], e);
        m_alloc.push_back(e);       
        m_trail.pop_back();
    }

    void viable::push_viable() {
        auto& [v, e] = m_trail.back();
        SASSERT(e->prev() != e || !m_viable[v]);
        SASSERT(e->prev() != e || e->next() == e);
        if (e->prev() != e) {
            e->prev()->insert_after(e);
            if (e->interval.lo_val() < e->next()->interval.lo_val())
                m_viable[v] = e;
        }
        else 
            m_viable[v] = e;        
        m_trail.pop_back();
    }

    bool viable::intersect(pvar v, signed_constraint const& c) {
        auto& fi = s.m_forbidden_intervals;
        entry* ne = alloc_entry();
        if (!fi.get_interval(c, v, ne->interval, ne->side_cond) || ne->interval.is_currently_empty()) {
            m_alloc.push_back(ne);
            return false;
        }
        else {
            ne->src = c;
            return intersect(v, ne);
        }
    }

    bool viable::intersect(pvar v, entry* ne) {
        entry* e = m_viable[v];
        if (e && e->interval.is_full()) {
            m_alloc.push_back(ne);
            return false;
        }

        if (ne->interval.is_currently_empty()) {
            m_alloc.push_back(ne);
            return false;
        }

        auto create_entry = [&]() {
            m_trail.push_back({ v, ne });
            s.m_trail.push_back(trail_instr_t::viable_add_i);
            ne->init(ne);            
            return ne;
        };

        auto remove_entry = [&](entry* e) {
            m_trail.push_back({ v, e });
            s.m_trail.push_back(trail_instr_t::viable_rem_i);
            e->remove_from(m_viable[v], e);
        };

        if (!e) 
            m_viable[v] = create_entry();
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
                    if (!m_viable[v]) {
                        m_viable[v] = create_entry();
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
                        m_viable[v] = e->prev();
                    SASSERT(well_formed(m_viable[v]));
                    return true;
                }
                e = e->next();
            }             
            while (e != first);
            // otherwise, append to end of list
            first->insert_before(create_entry());
        }
        SASSERT(well_formed(m_viable[v]));
        return true;
    }

    bool viable::has_viable(pvar v) {         
        auto* e = m_viable[v];
        if (!e)
            return true;
        entry* first = e;
        entry* last = e->prev();

        // quick check: last interval doesn't wrap around, so hi_val
        // has not been covered
        if (last->interval.lo_val() < last->interval.hi_val()) 
            return true;        
        
        do {
            if (e->interval.is_full())
                return false;
            entry* n = e->next();
            if (n == e)
                return true;
            if (!n->interval.currently_contains(e->interval.hi_val()))
                return true;
            if (n == first)
                return e->interval.lo_val() <= e->interval.hi_val();
            e = n;
        }         
        while (e != first);
        return false;
    }

    bool viable::is_viable(pvar v, rational const& val) { 
        auto* e = m_viable[v];
        if (!e)
            return true;
        entry* first = e;
        entry* last = first->prev();
        if (last->interval.currently_contains(val))
            return false;
        for (; e != last; e = e->next()) {        
            if (e->interval.currently_contains(val))
                return false;
            if (val < e->interval.lo_val())
                return true;
        }         
        return true; 
    }

    rational viable::min_viable(pvar v) { 
        rational lo(0);
        auto* e = m_viable[v];
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
        SASSERT(is_viable(v, lo));        
        return lo;
    }

    rational viable::max_viable(pvar v) { 
        rational hi = s.var2pdd(v).max_value();
        auto* e = m_viable[v];
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
        SASSERT(is_viable(v, hi));
        return hi;
    }

    dd::find_t viable::find_viable(pvar v, rational& lo) { 
        lo = 0;
        auto* e = m_viable[v];
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
        if (lo == hi)
            return dd::find_t::singleton;
        else
            return dd::find_t::multiple;
    }

    bool viable::resolve(pvar v, conflict& core) {
        if (has_viable(v))
            return false;
        auto* e = m_viable[v];
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
        if (!well_formed(m_viable[v]))
            LOG("v" << v << " not well formed");
        auto* e = m_viable[v];
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
        for (pvar v = 0; v < std::min(10u, m_viable.size()); ++v)
            log(v);
    }

    std::ostream& viable::display(std::ostream& out, pvar v) const {
        auto* e = m_viable[v];
        if (!e)
            return out;
        entry* first = e;
        do {
            out << "v" << v << ": " << e->interval << " " << e->side_cond << " " << e->src << "\n";
            e = e->next();
        }         
        while (e != first);
        return out;
    }

    std::ostream& viable::display(std::ostream& out) const {
        for (pvar v = 0; v < m_viable.size(); ++v)
            display(out, v);
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

