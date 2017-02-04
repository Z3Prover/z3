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
        m_out(0),
        m_inconsistent(false)
    {
        if (s.m_config.m_drat && s.m_config.m_drat_file != symbol()) {
            m_out = alloc(std::ofstream, s.m_config.m_drat_file.str().c_str());
        }
    }

    drat::~drat() {
        dealloc(m_out);
        for (unsigned i = 0; i < m_proof.size(); ++i) {
            clause* c = m_proof[i];
            if (m_status[i] == status::deleted || m_status[i] == status::external) {
                s.m_cls_allocator.del_clause(c);
            }
            else if (c && c->size() == 2) {
                s.m_cls_allocator.del_clause(c);
            }
        }
    }

    std::ostream& operator<<(std::ostream& out, drat::status st) {
        switch (st) {
        case drat::status::learned:  return out << "l";
        case drat::status::asserted: return out << "a";
        case drat::status::deleted:  return out << "d";
        default: return out;
        }
    }

    void drat::dump(unsigned n, literal const* c, status st) {
        if (is_cleaned(n, c)) return;
        switch (st) {
        case status::asserted: return;
        case status::learned: break;
        case status::deleted: (*m_out) << "d "; break;
        }
        literal last = null_literal;
        for (unsigned i = 0; i < n; ++i) {
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

    void drat::trace(std::ostream& out, unsigned n, literal const* c, status st) {
        out << st << " ";
        literal last = null_literal;
        for (unsigned i = 0; i < n; ++i) {
            declare(c[i]);
            if (c[i] != last) {
                out << c[i] << " ";
                last = c[i];
            }            
        }
        out << "\n";
    }

    void drat::append(literal l, status st) {
        trace(std::cout, 1, &l, st);
        if (st == status::learned) {
            verify(1, &l);
        }
        if (st == status::deleted) {
            return;
        }
        assign_propagate(l);
    }

    void drat::append(literal l1, literal l2, status st) {
        literal lits[2] = { l1, l2 };
        trace(std::cout, 2, lits, st);
        if (st == status::deleted) {
            // noop
            // don't record binary as deleted.
        }
        else {
            if (st == status::learned) {
                verify(2, lits);
            }
            clause* c = s.m_cls_allocator.mk_clause(2, lits, st == status::learned);
            m_proof.push_back(c);
            m_status.push_back(st);
            m_watches[(~l1).index()].push_back(c);
            m_watches[(~l2).index()].push_back(c);

            if (value(l1) == l_false && value(l2) == l_false) {
                m_inconsistent = true;
            }
            else if (value(l1) == l_false) {
                assign_propagate(l2);
            }
            else if (value(l2) == l_false) {
                assign_propagate(l1);
            }
        }
    }

    void drat::append(clause& c, status st) {
        unsigned n = c.size();
        if (is_cleaned(n, c.begin())) return;
        trace(std::cout, n, c.begin(), st);

        if (st == status::learned) {
            verify(n, c.begin());
        }

        m_status.push_back(st);
        m_proof.push_back(&c); 
        if (st == status::deleted) {
            del_watch(c, c[0]);
            del_watch(c, c[1]);
            return;
        }
        literal l1 = null_literal, l2 = null_literal;
        for (unsigned i = 0; i < n; ++i) {
            if (value(c[i]) != l_false) {
                if (l1 == null_literal) {
                    l1 = c[i];                    
                }
                else {
                    l2 = c[i];
                    break;
                }
            }
        }
        if (l2 == null_literal && l1 != null_literal) {
            assign_propagate(l1);
        }
        else if (l1 == null_literal) {
            m_inconsistent = true;
        }
        else {
            m_watches[(~l1).index()].push_back(&c);
            m_watches[(~l2).index()].push_back(&c);
        }
    }

    void drat::del_watch(clause& c, literal l) {
        watch& w = m_watches[(~l).index()];      
        for (unsigned i = 0; i < w.size(); ++i) {
            if (w[i] == &c) {
                w[i] = w.back();
                w.pop_back();
                break;
            }
        }
    }


    void drat::declare(literal l) {
        unsigned n = static_cast<unsigned>(l.var());
        while (m_assignment.size() <= n) {
            m_assignment.push_back(l_undef);
            m_watches.push_back(watch());
            m_watches.push_back(watch());
        }
    }

    void drat::verify(unsigned n, literal const* c) {
        if (m_inconsistent) {
            std::cout << "inconsistent\n";
            return;
        }
        unsigned num_units = m_units.size();
        for (unsigned i = 0; !m_inconsistent && i < n; ++i) {            
            assign_propagate(~c[i]);
        }
        for (unsigned i = num_units; i < m_units.size(); ++i) {
            m_assignment[m_units[i].var()] = l_undef;
        }
        m_units.resize(num_units);
        bool ok = m_inconsistent;
        m_inconsistent = false;
        if (ok) {
            std::cout << "Verified\n";
        }
        else {
            std::cout << "Verification failed\n";
            display(std::cout);
        }
    }

    void drat::display(std::ostream& out) const {
        out << "units: " << m_units << "\n";
#if 0
        for (unsigned i = 0; i < m_assignment.size(); ++i) {
            lbool v = value(literal(i, false));
            if (v != l_undef) std::cout << i << ": " << v << "\n";
        }
#endif
        for (unsigned i = 0; i < m_proof.size(); ++i) {
            clause* c = m_proof[i];
            if (m_status[i] != status::deleted && c) {
                out << i << ": " << *c << "\n";
            }
        }
#if 0
        for (unsigned i = 0; i < m_assignment.size(); ++i) {
            watch const& w1 = m_watches[2*i];
            watch const& w2 = m_watches[2*i + 1];
            if (!w1.empty()) {
                out << i << " |-> ";
                for (unsigned i = 0; i < w1.size(); ++i) out << w1[i] << " ";
                out << "\n";
            }
            if (!w2.empty()) {
                out << "-" << i << " |-> ";
                for (unsigned i = 0; i < w2.size(); ++i) out << w2[i] << " ";
                out << "\n";
            }
        }
#endif
    }

    lbool drat::value(literal l) const {
        lbool v = m_assignment[l.var()];
        return v == l_undef || !l.sign() ? v : ~v;
    }

    void drat::assign(literal l) {
        lbool new_value = l.sign() ? l_false : l_true;
        lbool old_value = value(l);
        if (new_value != old_value) {
            if (old_value == l_undef) {
                m_assignment[l.var()] = new_value;                
                m_units.push_back(l);
            }
            else {
                m_inconsistent = true;
            }
        }
    }

    void drat::assign_propagate(literal l) {
        unsigned num_units = m_units.size();
        assign(l);
        for (unsigned i = num_units; !m_inconsistent && i < m_units.size(); ++i) {
            propagate(m_units[i]);
        }        
    }

    void drat::propagate(literal l) {
        watch& clauses = m_watches[l.index()];
        watch::iterator it = clauses.begin();
        watch::iterator it2 = it;
        watch::iterator end = clauses.end();
        for (; it != end; ++it) {
            clause& c = *(*it);
            if (c[0] == ~l) {
                std::swap(c[0], c[1]);
            }
            if (c[1] != ~l) {
                *it2 = *it;
                it2++;
                continue;
            }
            SASSERT(c[1] == ~l);
            if (value(c[0]) == l_true) {
                it2++;
            }
            else {
                literal * l_it = c.begin() + 2;
                literal * l_end = c.end();
                bool done = false;
                for (; l_it != l_end && !done; ++l_it) {
                    if (value(*l_it) != l_false) {
                        c[1] = *l_it;
                        *l_it = ~l;
                        m_watches[(~c[1]).index()].push_back(&c);
                        done = true;
                    }
                }
                if (done) 
                    continue;                
                else if (value(c[0]) == l_false) {
                    m_inconsistent = true;
                    goto end_process_watch;
                }
                else {
                    *it2 = *it;
                    it2++;
                    assign(c[0]);
                }
            }
        }
    end_process_watch:
        for (; it != end; ++it, ++it2)          
            *it2 = *it;                         
        clauses.set_end(it2);                     
    }

    drat::status drat::get_status(bool learned) const {
        return learned || s.m_searching ? status::learned : status::asserted;
    }

    void drat::add() {
        if (m_out) (*m_out) << "0\n";
        if (s.m_config.m_drat_check) {
            if (m_inconsistent) std::cout << "Verified\n";
            else std::cout << "Failed to verify\n";
        }
    }
    void drat::add(literal l, bool learned) {
        status st = get_status(learned);
        if (m_out) dump(1, &l, st);
        if (s.m_config.m_drat_check) append(l, st);
    }
    void drat::add(literal l1, literal l2, bool learned) {
        literal ls[2] = {l1, l2};
        status st = get_status(learned);
        if (m_out) dump(2, ls, st);
        if (s.m_config.m_drat_check) append(l1, l2, st);
    }
    void drat::add(clause& c, bool learned) {
        status st = get_status(learned);
        if (m_out) dump(c.size(), c.begin(), st);
        if (s.m_config.m_drat_check) append(c, get_status(learned));
    }
    void drat::add(unsigned n, literal const* lits, unsigned m, premise * const* premises) {
        if (s.m_config.m_drat_check) {
            clause* c = s.m_cls_allocator.mk_clause(n, lits, true);
            append(*c, status::external);
        }        
    }
    void drat::del(literal l) {
        if (m_out) dump(1, &l, status::deleted);
        if (s.m_config.m_drat_check) append(l, status::deleted);
    }
    void drat::del(literal l1, literal l2) {
        literal ls[2] = {l1, l2};
        if (m_out) dump(2, ls, status::deleted);
        if (s.m_config.m_drat_check) append(l1, l2, status::deleted);
    }
    void drat::del(clause& c) {
        if (m_out) dump(c.size(), c.begin(), status::deleted);
        if (s.m_config.m_drat_check) append(c, status::deleted);
    }
}
