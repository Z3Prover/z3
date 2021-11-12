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

    viable2::~viable2() {}

    void viable2::pop_viable() {
        auto& [v, e] = m_trail.back();
        e->remove_from(m_viable[v], e);
        dealloc(e);
        m_trail.pop_back();
    }

    void viable2::intersect(pvar v, signed_constraint const& c) {
        entry* e = m_viable[v];
        if (e && e->interval.is_full())
            return;

        auto& fi = s.m_forbidden_intervals;
        fi_record r = { eval_interval::full(), {}, c };
        if (!fi.get_interval(c, v, r.interval, r.side_cond))
            return;

        auto create_entry = [&]() {
            entry* ne = alloc(entry);
            *static_cast<fi_record*>(ne) = r;
            ne->init(ne);
            m_trail.push_back({ v, ne });
            s.m_trail.push_back(trail_instr_t::viable_i);
            return ne;
        };

        if (!e) 
            m_viable[v] = create_entry();
        else {
            entry* first = e;
            do {
                if (e->interval.lo_val() == r.interval.lo_val() &&
                    e->interval.current_len() >= r.interval.current_len()) 
                    return;                
                if (e->interval.lo_val() >= r.interval.lo_val()) {
                    e->insert_before(create_entry());
                    if (e == first)
                        m_viable[v] = e->prev();
                    return;
                }
                e = e->next();
            }             
            while (e != first);
            // otherwise, append to end of list
            first->insert_before(create_entry());
        }
        SASSERT(is_sorted(m_viable[v]));
    }

    bool viable2::has_viable(pvar v) { 
        auto* e = m_viable[v];
        if (!e)
            return true;
        entry* first = e;
        rational lo(0);
        do {
            if (e->interval.is_full())
                return false;
            if (!e->interval.currently_contains(lo))
                return true;
            lo = e->interval.hi_val();            
            e = e->next();
        }         
        while (e != first);
        // ???
        return !first->prev()->interval.currently_contains(lo) &&
            first->interval.hi_val() <= lo;
    }

    bool viable2::is_viable(pvar v, rational const& val) { 
        auto* e = m_viable[v];
        if (!e)
            return true;
        entry* first = e;
        do {
            if (e->interval.currently_contains(val))
                return false;
            e = e->next();
        }         
        while (e != first);
        return true; 
    }

    void viable2::add_non_viable(pvar v, rational const& val) { 
        NOT_IMPLEMENTED_YET();
    }

    rational viable2::min_viable(pvar v) { 
        return rational::zero(); 
    }

    rational viable2::max_viable(pvar v) { 
        return rational::zero(); 
    }

    dd::find_t viable2::find_viable(pvar v, rational& val) { 
        auto* e = m_viable[v];
        val = 0;
        if (!e) 
            return dd::find_t::multiple;
        
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

    bool viable2::is_sorted(entry* e) {
        entry* first = e;
        while (true) {
            if (e->interval.is_full())
                return true;
            auto* n = e->next();
            if (n == first)
                break;
            if (e->interval.lo_val() > n->interval.lo_val())
                return false;
            if (e->interval.lo_val() == n->interval.lo_val() &&
                e->interval.current_len() > n->interval.current_len())
                return false;
            e = n;
        }
        return true;
    }


}

