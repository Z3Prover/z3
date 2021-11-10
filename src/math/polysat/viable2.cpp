/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    maintain viable domains

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6


--*/


#include "math/polysat/viable2.h"
#include "math/polysat/solver.h"


namespace polysat {

    viable2::viable2(solver& s) : s(s) {}

    viable2::~viable2() {}

    void viable2::push_viable(pvar v) {
        m_trail.push_back(std::make_pair(v, m_viable[v]));
    }

    void viable2::pop_viable() {
        auto const& [v, s] = m_trail.back();
        m_viable[v] = s;
        m_trail.pop_back();
    }

    void viable2::intersect(pvar v, signed_constraint const& c) {
        auto& fi = s.m_forbidden_intervals;
        vector<signed_constraint> side_cond;
        eval_interval interval = eval_interval::full();
        if (!fi.get_interval(c, v, interval, side_cond))
            return;
        auto& s = m_viable[v];
        for (unsigned i = 0; i < s.size(); ++i) {

        }
    }

    bool viable2::has_viable(pvar v) { return true; }

    bool viable2::is_viable(pvar v, rational const& val) { return true; }

    void viable2::add_non_viable(pvar v, rational const& val) { }

    rational viable2::min_viable(pvar v) { return rational::zero(); }

    rational viable2::max_viable(pvar v) { return rational::zero(); }

    dd::find_t viable2::find_viable(pvar v, rational& val) { return dd::find_t::multiple; }

    void viable2::log(pvar v) {
        auto const& s = m_viable[v];
        for (auto const& [i, c] : s) 
            LOG("v" << v << ": " << i);        
    }

    void viable2::log() {
        for (pvar v = 0; v < std::min(10u, m_viable.size()); ++v)
            log(v);
    }


}

