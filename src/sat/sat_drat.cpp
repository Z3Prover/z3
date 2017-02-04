/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    sat_drat.cpp

Abstract:
   
    Produce DRAT proofs.

    Check them using a very simple forward checker 
    that interacts with external plugins.

Author:

    Nikolaj Bjorner (nbjorner) 2017-2-3

Notes:

--*/
#include "sat_solver.h"
#include "sat_drat.h"


namespace sat {
    drat::drat(solver& s):
        s(s),
        m_out(0)
    {
        if (s.m_config.m_drat && s.m_config.m_drat_file != symbol()) {
            m_out = alloc(std::ofstream, s.m_config.m_drat_file.str().c_str());
        }
    }

    drat::~drat() {
        dealloc(m_out);
    }

    std::ostream& operator<<(std::ostream& out, drat::status st) {
        switch (st) {
        case drat::status::learned:  return out << "l";
        case drat::status::asserted: return out << "a";
        case drat::status::deleted:  return out << "d";
        default: return out;
        }
    }

    void drat::dump(unsigned sz, literal const* c, status st) {
        if (is_cleaned(sz, c)) return;
        switch (st) {
        case status::asserted: return;
        case status::learned: break;
        case status::deleted: (*m_out) << "d "; break;
        }
        literal last = null_literal;
        for (unsigned i = 0; i < sz; ++i) {
            if (c[i] != last) {
                (*m_out) << c[i] << " ";
                last = c[i];
            }
        }
        (*m_out) << "0\n";
    }

    bool drat::is_cleaned(unsigned n, literal const* c) const {
        literal last = null_literal;
        for (unsigned i = 0; i < n; ++i) {
            if (c[i] == last) return true;
            last = c[i];
        }
        return false;
    }

    void drat::append(unsigned n, literal const* c, status st) {
        if (is_cleaned(n, c)) return;
        m_status.push_back(st);
        m_proof.push_back(0); // TBD


        std::cout << st << " ";
        literal last = null_literal;
        for (unsigned i = 0; i < n; ++i) {
            if (c[i] != last) {
                std::cout << c[i] << " ";
                last = c[i];
            }
            
        }
        std::cout << "\n";
    }

    drat::status drat::get_status(bool learned) const {
        return learned || s.m_searching ? status::learned : status::asserted;
    }

    void drat::add() {
        if (m_out) (*m_out) << "0\n";
        if (s.m_config.m_drat_check) append(0, 0, status::learned);
    }
    void drat::add(literal l, bool learned) {
        status st = get_status(learned);
        if (m_out) dump(1, &l, st);
        if (s.m_config.m_drat_check) append(1, &l, st);
    }
    void drat::add(literal l1, literal l2, bool learned) {
        literal ls[2] = {l1, l2};
        status st = get_status(learned);
        if (m_out) dump(2, ls, st);
        if (s.m_config.m_drat_check) append(2, ls, st);
    }
    void drat::add(literal l1, literal l2, literal l3, bool learned) {
        literal ls[3] = {l1, l2, l3};
        status st = get_status(learned);
        if (m_out) dump(3, ls, st);
        if (s.m_config.m_drat_check) append(3, ls, get_status(learned));
    }
    void drat::add(clause& c, bool learned) {
        status st = get_status(learned);
        if (m_out) dump(c.size(), c.begin(), st);
        if (s.m_config.m_drat_check) append(c.size(), c.begin(), get_status(learned));
    }
    void drat::del(literal l) {
        if (m_out) dump(1, &l, status::deleted);
        if (s.m_config.m_drat_check) append(1, &l, status::deleted);
    }
    void drat::del(literal l1, literal l2) {
        literal ls[2] = {l1, l2};
        if (m_out) dump(2, ls, status::deleted);
        if (s.m_config.m_drat_check) append(2, ls, status::deleted);
    }
    void drat::del(clause& c) {
        if (m_out) dump(c.size(), c.begin(), status::deleted);
        if (s.m_config.m_drat_check) append(c.size(), c.begin(), status::deleted);
    }
}
