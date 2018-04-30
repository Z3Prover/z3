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
        m_inconsistent(false),
        m_check_unsat(false),
        m_check_sat(false),
        m_check(false)
    {
        if (s.m_config.m_drat && s.m_config.m_drat_file != symbol()) {
            m_out = alloc(std::ofstream, s.m_config.m_drat_file.str().c_str());
        }
    }

    drat::~drat() {
        dealloc(m_out);
        for (unsigned i = 0; i < m_proof.size(); ++i) {
            clause* c = m_proof[i];
            if (c && (c->size() == 2 || m_status[i] == status::deleted || m_status[i] == status::external)) {
                s.dealloc_clause(c);
            }
        }
    }

    void drat::updt_config() {
        m_check_unsat = s.m_config.m_drat_check_unsat;
        m_check_sat = s.m_config.m_drat_check_sat;
        m_check = m_check_unsat || m_check_sat;
    }

    std::ostream& operator<<(std::ostream& out, drat::status st) {
        switch (st) {
        case drat::status::learned:  return out << "l";
        case drat::status::asserted: return out << "a";
        case drat::status::deleted:  return out << "d";
        case drat::status::external: return out << "e";
        default: return out;
        }
    }

    void drat::dump(unsigned n, literal const* c, status st) {
        switch (st) {
        case status::asserted: return;
        case status::external: return; // requires extension to drat format.
        case status::learned: break;
        case status::deleted: (*m_out) << "d "; break;
        }
        for (unsigned i = 0; i < n; ++i) (*m_out) << c[i] << " ";
        (*m_out) << "0\n";
    }

    bool drat::is_cleaned(clause& c) const {
        literal last = null_literal;
        unsigned n = c.size();
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
            if (c[i] != last) {
                out << c[i] << " ";
                last = c[i];
            }            
        }
        out << "\n";
    }

    void drat::append(literal l, status st) {
        IF_VERBOSE(20, trace(verbose_stream(), 1, &l, st););
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
        IF_VERBOSE(20, trace(verbose_stream(), 2, lits, st););
        if (st == status::deleted) {
            // noop
            // don't record binary as deleted.
        }
        else {
            if (st == status::learned) {
                verify(2, lits);
            }
            clause* c = s.alloc_clause(2, lits, st == status::learned);
            m_proof.push_back(c);
            m_status.push_back(st);
            unsigned idx = m_watched_clauses.size();
            m_watched_clauses.push_back(watched_clause(c, l1, l2));
            m_watches[(~l1).index()].push_back(idx);
            m_watches[(~l2).index()].push_back(idx);

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
        IF_VERBOSE(20, trace(verbose_stream(), n, c.begin(), st););

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
        unsigned num_watch = 0;
        literal l1, l2;
        for (unsigned i = 0; i < n; ++i) {
            if (value(c[i]) != l_false) {
                if (num_watch == 0) {
                    l1 = c[i];
                    ++num_watch;
                }
                else {
                    l2 = c[i];
                    ++num_watch;
                    break;
                }
            }
        }
        switch (num_watch) {
        case 0: 
            m_inconsistent = true; 
            break;
        case 1: 
            assign_propagate(l1); 
            break;
        default: {
            SASSERT(num_watch == 2);
            unsigned idx = m_watched_clauses.size();
            m_watched_clauses.push_back(watched_clause(&c, l1, l2));
            m_watches[(~l1).index()].push_back(idx);
            m_watches[(~l2).index()].push_back(idx);
            break;
        }
        }
    }

    void drat::del_watch(clause& c, literal l) {
        watch& w = m_watches[(~l).index()];      
        for (unsigned i = 0; i < w.size(); ++i) {
            if (m_watched_clauses[w[i]].m_clause == &c) {
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

    bool drat::is_drup(unsigned n, literal const* c) {
        if (m_inconsistent || n == 0) return true;
        unsigned num_units = m_units.size();
        for (unsigned i = 0; !m_inconsistent && i < n; ++i) {            
            assign_propagate(~c[i]);
        }
        if (!m_inconsistent) {
            DEBUG_CODE(validate_propagation(););
        }
        for (unsigned i = 0; i < m_units.size(); ++i) {
            SASSERT(m_assignment[m_units[i].var()] != l_undef);
        }

        for (unsigned i = num_units; i < m_units.size(); ++i) {
            m_assignment[m_units[i].var()] = l_undef;
        }
        m_units.resize(num_units);
        bool ok = m_inconsistent;
        m_inconsistent = false;
        return ok;
    }

    bool drat::is_drat(unsigned n, literal const* c) {
        if (m_inconsistent || n == 0) return true;
        for (unsigned i = 0; i < n; ++i) {
            if (is_drat(n, c, i)) return true;
        }
        return false;
    }

    void drat::validate_propagation() const {
        for (unsigned i = 0; i < m_proof.size(); ++i) {
            status st = m_status[i];
            if (m_proof[i] && st != status::deleted) {
                clause& c = *m_proof[i];
                unsigned num_undef = 0, num_true = 0;
                for (unsigned j = 0; j < c.size(); ++j) {
                    switch (value(c[j])) {
                    case l_false: break;
                    case l_true: num_true++; break;
                    case l_undef: num_undef++; break;
                    }
                }
                CTRACE("sat", num_true == 0 && num_undef == 1, display(tout););
                SASSERT(num_true != 0 || num_undef != 1);
            }
        }
    }

    bool drat::is_drat(unsigned n, literal const* c, unsigned pos) {
        SASSERT(pos < n);
        literal l = c[pos];
        literal_vector lits(n, c);
        SASSERT(lits.size() == n);
        for (unsigned i = 0; i < m_proof.size(); ++i) {
            status st = m_status[i];
            if (m_proof[i] && (st == status::asserted || st == status::external)) {
                clause& c = *m_proof[i];
                unsigned j = 0;
                for (; j < c.size() && c[j] != ~l; ++j) {}
                if (j != c.size()) {
                    lits.append(j, c.begin());
                    lits.append(c.size() - j - 1, c.begin() + j + 1);
                    if (!is_drup(lits.size(), lits.c_ptr())) return false;
                    lits.resize(n);
                }
            }
        }
        return true;

    }

    void drat::verify(unsigned n, literal const* c) {
        if (m_check_unsat && !is_drup(n, c) && !is_drat(n, c)) {
            std::cout << "Verification failed\n";
            UNREACHABLE();
            //display(std::cout);
            TRACE("sat", 
                  tout << literal_vector(n, c) << "\n";
                  display(tout); 
                  s.display(tout););
            UNREACHABLE();
            exit(0);
        }
    }

    void drat::display(std::ostream& out) const {
        out << "units: " << m_units << "\n";
        for (unsigned i = 0; i < m_assignment.size(); ++i) {
            lbool v = value(literal(i, false));            
            if (v != l_undef) out << i << ": " << v << "\n";
        }
        for (unsigned i = 0; i < m_proof.size(); ++i) {
            clause* c = m_proof[i];
            if (m_status[i] != status::deleted && c) {
                unsigned num_true = 0;
                unsigned num_undef = 0;
                for (unsigned j = 0; j < c->size(); ++j) {
                    switch (value((*c)[j])) {
                    case l_true: num_true++; break;
                    case l_undef: num_undef++; break;
                    default: break;
                    }
                }
                if (num_true == 0 && num_undef == 0) {
                    out << "False ";
                }
                if (num_true == 0 && num_undef == 1) {
                    out << "Unit ";
                }
                out << m_status[i] << " " << i << ": " << *c << "\n";
            }
        }
        for (unsigned i = 0; i < m_assignment.size(); ++i) {
            watch const& w1 = m_watches[2*i];
            watch const& w2 = m_watches[2*i + 1];
            if (!w1.empty()) {
                out << i << " |-> ";
                for (unsigned i = 0; i < w1.size(); ++i) out << *(m_watched_clauses[w1[i]].m_clause) << " ";
                out << "\n";
            }
            if (!w2.empty()) {
                out << "-" << i << " |-> ";
                for (unsigned i = 0; i < w2.size(); ++i) out << *(m_watched_clauses[w2[i]].m_clause) << " ";
                out << "\n";
            }
        }
    }

    lbool drat::value(literal l) const {
        lbool val = m_assignment.get(l.var(), l_undef);
        return val == l_undef || !l.sign() ? val : ~val;
    }

    void drat::assign(literal l) {
        lbool new_value = l.sign() ? l_false : l_true;
        lbool old_value = value(l);
//        TRACE("sat", tout << "assign " << l << " := " << new_value << " from " << old_value << "\n";);
        switch (old_value) {
        case l_false:
            m_inconsistent = true;
            break;
        case l_true:
            break;
        case l_undef:
            m_assignment.setx(l.var(), new_value, l_undef);
            m_units.push_back(l);
            break;
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
            unsigned idx = *it;
            watched_clause& wc = m_watched_clauses[idx];
            clause& c = *wc.m_clause;

            //TRACE("sat", tout << "Propagate " << l << " " << c << " watch: " << wc.m_l1 << " " << wc.m_l2 << "\n";);
            if (wc.m_l1 == ~l) {
                std::swap(wc.m_l1, wc.m_l2);
            }

            SASSERT(wc.m_l2 == ~l);
            if (value(wc.m_l1) == l_true) {
                *it2 = *it;
                it2++;
            }
            else {
                bool done = false;
                for (unsigned i = 0; !done && i < c.size(); ++i) {
                    literal lit = c[i];
                    if (lit != wc.m_l1 && lit != wc.m_l2 && value(lit) != l_false) {
                        wc.m_l2 = lit;
                        m_watches[(~lit).index()].push_back(idx);
                        done = true;
                    } 
                }
                if (done) {
                    continue;                
                }
                else if (value(wc.m_l1) == l_false) {
                    m_inconsistent = true;
                    goto end_process_watch;
                }
                else {
                    *it2 = *it;
                    it2++;
                    assign(wc.m_l1);
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
        if (m_check_unsat) {
            SASSERT(m_inconsistent);
        }
    }
    void drat::add(literal l, bool learned) {
        declare(l);
        status st = get_status(learned);
        if (m_out) dump(1, &l, st);
        if (m_check) append(l, st);
    }
    void drat::add(literal l1, literal l2, bool learned) {
        declare(l1);
        declare(l2);
        literal ls[2] = {l1, l2};
        status st = get_status(learned);
        if (m_out) dump(2, ls, st);
        if (m_check) append(l1, l2, st);
    }
    void drat::add(clause& c, bool learned) {
        TRACE("sat", tout << "add: " << c << "\n";);
        for (unsigned i = 0; i < c.size(); ++i) declare(c[i]);
        status st = get_status(learned);
        if (m_out) dump(c.size(), c.begin(), st);
        if (m_check_unsat) append(c, get_status(learned));
    }
    void drat::add(literal_vector const& lits, svector<premise> const& premises) {
        if (m_check) {
            switch (lits.size()) {
            case 0: add(); break;
            case 1: append(lits[0], status::external); break;
            default: {
                clause* c = s.alloc_clause(lits.size(), lits.c_ptr(), true);
                append(*c, status::external);
                break;
            }
            }
        }                        
    }
    void drat::add(literal_vector const& c) {
        for (unsigned i = 0; i < c.size(); ++i) declare(c[i]);
        if (m_out) dump(c.size(), c.begin(), status::learned);
        if (m_check) {
            switch (c.size()) {
            case 0: add(); break;
            case 1: append(c[0], status::learned); break;
            default: {
                verify(c.size(), c.begin());
                clause* cl = s.alloc_clause(c.size(), c.c_ptr(), true);
                append(*cl, status::external);                
                break;
            }
            }
        }
    }

    void drat::del(literal l) {
        if (m_out) dump(1, &l, status::deleted);
        if (m_check_unsat) append(l, status::deleted);
    }
    void drat::del(literal l1, literal l2) {
        literal ls[2] = {l1, l2};
        if (m_out) dump(2, ls, status::deleted);
        if (m_check) 
            append(l1, l2, status::deleted);
    }
    void drat::del(clause& c) {
        TRACE("sat", tout << "del: " << c << "\n";);
        if (m_out) dump(c.size(), c.begin(), status::deleted);
        if (m_check) {
            clause* c1 = s.alloc_clause(c.size(), c.begin(), c.is_learned()); 
            append(*c1, status::deleted);
        }
    }
    
    void drat::check_model(model const& m) {
        std::cout << "check model on " << m_proof.size() << "\n";
    }

}
