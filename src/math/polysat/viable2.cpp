/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    maintain viable domains

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6


--*/


#include "util/debug.h"
#include "math/polysat/viable2.h"
#include "math/polysat/solver.h"


namespace polysat {

    viable2::viable2(solver& s) : s(s) {}

    viable2::~viable2() {
        for (entry* e : m_alloc)
            dealloc(e);
    }

    viable2::entry* viable2::alloc_entry() {
        if (m_alloc.empty())
            return alloc(entry);
        auto* e = m_alloc.back();
        m_alloc.pop_back();
        return e;
    }

    void viable2::pop_viable() {
        auto& [v, e] = m_trail.back();
        e->remove_from(m_viable[v], e);
        m_alloc.push_back(e);       
        m_trail.pop_back();
    }

    void viable2::push_viable() {
        auto& [v, e] = m_trail.back();
        if (e->prev() != e) 
            e->prev()->insert_after(e);        
        else {
            SASSERT(!m_viable[v]);
            SASSERT(e->next() == e);
            m_viable[v] = e;
        }
        m_trail.pop_back();
    }

    void viable2::intersect(pvar v, signed_constraint const& c) {
        entry* e = m_viable[v];
        if (e && e->interval.is_full())
            return;

        auto& fi = s.m_forbidden_intervals;
        entry* ne = alloc_entry();
        if (!fi.get_interval(c, v, ne->interval, ne->side_cond)) {
            m_alloc.push_back(ne);
            return;
        }
        ne->init(ne);

        auto create_entry = [&]() {
            m_trail.push_back({ v, ne });
            s.m_trail.push_back(trail_instr_t::viable_add_i);
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
                    return;
                }
                if (ne->interval.contains(e->interval)) {
                    entry* n = e->next();
                    remove_entry(e);
                    if (e == n) {
                        m_viable[v] = create_entry();
                        break;
                    }
                    e = n;
                    continue;
                }             
                SASSERT(e->interval.lo_val() != ne->interval.lo_val());
                if (e->interval.lo_val() >= ne->interval.lo_val()) {
                    e->insert_before(create_entry());
                    if (e == first)
                        m_viable[v] = e->prev();
                    SASSERT(well_formed(m_viable[v]));
                    return;
                }
                e = e->next();
            }             
            while (e != first);
            // otherwise, append to end of list
            first->insert_before(create_entry());
        }
        SASSERT(well_formed(m_viable[v]));
    }

    bool viable2::has_viable(pvar v) { 
        auto* e = m_viable[v];
        if (!e)
            return true;
        entry* first = e;
        do {
            if (e->interval.is_full())
                return false;
            entry* n = e->next();
            if (n == e)
                return true;
            if (n == first)
                return e->interval.hi_val() != e->interval.hi().manager().max_value();

            if (e->interval.hi_val() < n->interval.lo_val())
                return true;
            e = n;
        }         
        while (e != first);
        return false;
    }

    bool viable2::is_viable(pvar v, rational const& val) { 
        auto* e = m_viable[v];
        if (!e)
            return true;
        entry* first = e;
        do {
            if (e->interval.currently_contains(val))
                return false;
            if (e->interval.lo_val() < val)
                return !first->prev()->interval.currently_contains(val);
            e = e->next();
        }         
        while (e != first);
        return true; 
    }

    void viable2::add_non_viable(pvar v, rational const& val) { 
        NOT_IMPLEMENTED_YET();
    }

    rational viable2::min_viable(pvar v) { 
        rational lo(0);
        auto* e = m_viable[v];
        if (!e)
            return lo;
        entry* first = e;
        if (first->prev()->interval.currently_contains(lo))
            lo = first->prev()->interval.hi_val();
        do {
            if (!e->interval.currently_contains(lo))
                return lo;
            lo = e->interval.hi_val();
            e = e->next();
        }         
        while (e != first);
        return lo;
    }

    rational viable2::max_viable(pvar v) { 
        return rational::zero(); 
    }

    dd::find_t viable2::find_viable(pvar v, rational& val) { 
        auto* e = m_viable[v];
        val = 0;
        if (!e) 
            return dd::find_t::multiple;


        entry* first = e;
        do {
            if (e->interval.is_full())
                return dd::find_t::empty;
            entry* n = e->next();
            if (n == e && e->interval.lo_val() != 0) {
                val = 0;
                if (e->interval.lo_val() > 1 || e->interval.hi_val() < e->interval.hi().manager().max_value())
                    return dd::find_t::multiple;
                return dd::find_t::singleton;
            }
            if (n == first) {
                if (e->interval.hi_val() == e->interval.hi().manager().max_value())
                    ;
            }
            e = n;
        }         
        while (e != first);
        
#if 0
        // TODO
        entry* first = e;
        do {
            if (e->interval.is_full())
                return dd::find_t::empty;
            if (e->interval.currently_contains(val)) {
                val = e->interval.hi_val();
            }
        }         
        while (e != first);
#endif

        return dd::find_t::multiple;
    }

    void viable2::log(pvar v) {
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

    void viable2::log() {
        for (pvar v = 0; v < std::min(10u, m_viable.size()); ++v)
            log(v);
    }

    /*
    * Lower bounds are strictly ascending.
    * intervals don't contain each-other (since lower bounds are ascending, 
    * it suffices to check containment in one direction).
    */
    bool viable2::well_formed(entry* e) {
        entry* first = e;
        while (true) {
            if (e->interval.is_full())
                return e->next() == e;
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

