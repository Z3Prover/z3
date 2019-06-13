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
        m_out(nullptr),
        m_bout(nullptr),
        m_inconsistent(false),
        m_check_unsat(false),
        m_check_sat(false),
        m_check(false)
    {
        if (s.m_config.m_drat && s.m_config.m_drat_file != symbol()) {
            auto mode = s.m_config.m_drat_binary ? (std::ios_base::binary | std::ios_base::out | std::ios_base::trunc) : std::ios_base::out;
            m_out = alloc(std::ofstream, s.m_config.m_drat_file.str().c_str(), mode);
            if (s.m_config.m_drat_binary) {
                std::swap(m_out, m_bout);
            }
        }
    }

    drat::~drat() {
        if (m_out) m_out->flush();
        if (m_bout) m_bout->flush();
        dealloc(m_out);
        dealloc(m_bout);
        for (unsigned i = 0; i < m_proof.size(); ++i) {
            clause* c = m_proof[i];
            if (c) {
                m_alloc.del_clause(c);
            }
        }
        m_proof.reset();
        m_out = nullptr;
        m_bout = nullptr;
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
        if (st == status::asserted || st == status::external) {
            return;
        }
        
        char buffer[10000];
        char digits[20];     // enough for storing unsigned
        char* lastd = digits + sizeof(digits);
        
        unsigned len = 0;
        if (st == status::deleted) {
            buffer[0] = 'd';
            buffer[1] = ' ';
            len = 2;
        }
        for (unsigned i = 0; i < n; ++i) {
            literal lit = c[i];
            unsigned v = lit.var();            
            if (lit.sign()) buffer[len++] = '-';
            char* d = lastd;
            while (v > 0) {                
                d--;
                *d = (v % 10) + '0';
                v /= 10;
                SASSERT(d > digits);
            }
	    SASSERT(len + lastd < sizeof(buffer) + d);
	    memcpy(buffer + len, d, lastd - d);
	    len += static_cast<unsigned>(lastd - d);            
	    buffer[len++] = ' ';
	    if (len + 50 > sizeof(buffer)) {
	        m_out->write(buffer, len);
	        len = 0;
            }
        }        
	buffer[len++] = '0';
	buffer[len++] = '\n';
	m_out->write(buffer, len);               
    }

    void drat::bdump(unsigned n, literal const* c, status st) {
        unsigned char ch = 0;
        switch (st) {
        case status::asserted: return;
        case status::external: return; 
        case status::learned: ch = 'a'; break;
        case status::deleted: ch = 'd'; break;
        default: UNREACHABLE(); break;
        }
        char buffer[10000];
        int len = 0;
        buffer[len++] = ch;

        for (unsigned i = 0; i < n; ++i) {
            literal lit = c[i];
            unsigned v = 2 * lit.var() + (lit.sign() ? 1 : 0);
            do {
                ch = static_cast<unsigned char>(v & 255);
                v >>= 7;
                if (v) ch |= 128;
                buffer[len++] = ch;
                if (len == sizeof(buffer)) {
                    m_bout->write(buffer, len);
                    len = 0;
                }
            }
            while (v);
        }
        buffer[len++] = 0;
        m_bout->write(buffer, len);
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
        TRACE("sat_drat", tout << st << " " << l << "\n";);

        declare(l);
        IF_VERBOSE(20, trace(verbose_stream(), 1, &l, st););
        if (st == status::learned) {
            verify(1, &l);
        }
        if (st == status::deleted) {
            return;
        }
        if (m_check_unsat) {
            assign_propagate(l);
        }

        m_units.push_back(l);
    }

    void drat::append(literal l1, literal l2, status st) {
        TRACE("sat_drat", tout << st << " " << l1 << " " << l2 << "\n";);
        declare(l1); 
        declare(l2);
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
            clause* c = m_alloc.mk_clause(2, lits, st == status::learned);
            m_proof.push_back(c);
            m_status.push_back(st);
            if (!m_check_unsat) return;
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

#if 0
    // debugging code
    bool drat::is_clause(clause& c, literal l1, literal l2, literal l3, drat::status st1, drat::status st2) {
        //if (st1 != st2) return false;
        if (c.size() != 3) return false;
        if (l1 == c[0]) {
            if (l2 == c[1] && l3 == c[2]) return true;
            if (l2 == c[2] && l3 == c[1]) return true;
        }
        if (l2 == c[0]) {
            if (l1 == c[1] && l3 == c[2]) return true;
            if (l1 == c[2] && l3 == c[1]) return true;
        }
        if (l3 == c[0]) {
            if (l1 == c[1] && l2 == c[2]) return true;
            if (l1 == c[2] && l2 == c[1]) return true;
        }
        return false;
    }
#endif

    void drat::append(clause& c, status st) {
        TRACE("sat_drat", tout << st << " " << c << "\n";);
        for (literal lit : c) declare(lit);
        unsigned n = c.size();
        IF_VERBOSE(20, trace(verbose_stream(), n, c.begin(), st););

        if (st == status::learned) {
            verify(c);
        }
           
        m_status.push_back(st);
        m_proof.push_back(&c); 
        if (st == status::deleted) {
            if (n > 0) del_watch(c, c[0]);
            if (n > 1) del_watch(c, c[1]);
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
        if (!m_check) return;
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
        DEBUG_CODE(
            for (literal u : m_units) {
                SASSERT(m_assignment[u.var()] != l_undef);
            });

#if 0
        if (!m_inconsistent) {
            literal_vector lits(n, c);
            IF_VERBOSE(0, verbose_stream() << "not drup " << lits << "\n");
            for (unsigned v = 0; v < m_assignment.size(); ++v) {
                lbool val = m_assignment[v];
                if (val != l_undef) {
                    IF_VERBOSE(0, verbose_stream() << literal(v, false) << " |-> " << val << "\n");
                }
            }
            for (clause* cp : s.m_clauses) {
                clause& cl = *cp;
                bool found = false;
                for (literal l : cl) {
                    if (m_assignment[l.var()] != (l.sign() ? l_true : l_false)) {
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    IF_VERBOSE(0, verbose_stream() << "Clause is false under assignment: " << cl << "\n");
                }
            }
            for (clause* cp : s.m_learned) {
                clause& cl = *cp;
                bool found = false;
                for (literal l : cl) {
                    if (m_assignment[l.var()] != (l.sign() ? l_true : l_false)) {
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    IF_VERBOSE(0, verbose_stream() << "Clause is false under assignment: " << cl << "\n");
                }
            }
            svector<sat::solver::bin_clause> bin;
            s.collect_bin_clauses(bin, true);
            for (auto & b : bin) {
                bool found = false;
                if (m_assignment[b.first.var()] != (b.first.sign() ? l_true : l_false)) found = true;
                if (m_assignment[b.second.var()] != (b.second.sign() ? l_true : l_false)) found = true;
                if (!found) {
                    IF_VERBOSE(0, verbose_stream() << "Bin clause is false under assignment: " << b.first << " " << b.second << "\n");
                }
            }
            IF_VERBOSE(0, s.display(verbose_stream()));
            exit(0);
        }
#endif

        for (unsigned i = num_units; i < m_units.size(); ++i) {
            m_assignment[m_units[i].var()] = l_undef;
        }
        m_units.shrink(num_units);
        bool ok = m_inconsistent;
        IF_VERBOSE(9, verbose_stream() << "is-drup " << m_inconsistent << "\n");
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
            if (m_proof[i] && m_proof[i]->size() > 1 && st != status::deleted) {
                clause& c = *m_proof[i];
                unsigned num_undef = 0, num_true = 0;
                for (unsigned j = 0; j < c.size(); ++j) {
                    switch (value(c[j])) {
                    case l_false: break;
                    case l_true: num_true++; break;
                    case l_undef: num_undef++; break;
                    }
                }
                CTRACE("sat_drat", num_true == 0 && num_undef == 1, display(tout););
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
            if (m_proof[i] && m_proof[i]->size() > 1 && (st == status::asserted || st == status::external)) {
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
        if (!m_check_unsat) {
            return;
        }
        for (unsigned i = 0; i < n; ++i) { 
            declare(c[i]);
        } 
        if (!is_drup(n, c) && !is_drat(n, c)) {
            literal_vector lits(n, c);
            std::cout << "Verification of " << lits << " failed\n";
            s.display(std::cout);
            SASSERT(false);
            exit(0);
            UNREACHABLE();
            //display(std::cout);
            TRACE("sat_drat", 
                  tout << literal_vector(n, c) << "\n";
                  display(tout); 
                  s.display(tout););
            UNREACHABLE();
        }
    }

    bool drat::contains(literal c, justification const& j) {
        if (!m_check_sat) {
            return true;
        }
        switch (j.get_kind()) {
        case justification::NONE:
            return m_units.contains(c);
        case justification::BINARY:
            return contains(c, j.get_literal());
        case justification::TERNARY:
            return contains(c, j.get_literal1(), j.get_literal2());
        case justification::CLAUSE: 
            return contains(s.get_clause(j));
        default:
            return true;
        }
    }

    bool drat::contains(unsigned n, literal const* lits) {
        if (!m_check) return true;
        unsigned num_add = 0;
        unsigned num_del = 0;
        for (unsigned i = m_proof.size(); i-- > 0; ) {
            clause& c = *m_proof[i];
            status st = m_status[i];
            if (match(n, lits, c)) {
                if (st == status::deleted) {
                    num_del++;
                } 
                else {
                    num_add++;
                }
            }
        }
        return num_add > num_del;
    }

    bool drat::match(unsigned n, literal const* lits, clause const& c) const {
        if (n == c.size()) {
            for (unsigned i = 0; i < n; ++i) {
                literal lit1 = lits[i];
                bool found = false;
                for (literal lit2 : c) {
                    if (lit1 == lit2) {
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    return false;
                }
            }
            return true;
        }
        return false;
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
//        TRACE("sat_drat", tout << "assign " << l << " := " << new_value << " from " << old_value << "\n";);
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

            //TRACE("sat_drat", tout << "Propagate " << l << " " << c << " watch: " << wc.m_l1 << " " << wc.m_l2 << "\n";);
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
        if (m_bout) bdump(0, nullptr, status::learned);
        if (m_check_unsat) {
            SASSERT(m_inconsistent);
        }
    }
    void drat::add(literal l, bool learned) {
        status st = get_status(learned);
        if (m_out) dump(1, &l, st);
        if (m_bout) bdump(1, &l, st);
        if (m_check) append(l, st);
    }
    void drat::add(literal l1, literal l2, bool learned) {
        literal ls[2] = {l1, l2};
        status st = get_status(learned);
        if (m_out) dump(2, ls, st);
        if (m_bout) bdump(2, ls, st);
        if (m_check) append(l1, l2, st);
    }
    void drat::add(clause& c, bool learned) {
        status st = get_status(learned);
        if (m_out) dump(c.size(), c.begin(), st);
        if (m_bout) bdump(c.size(), c.begin(), st);
        if (m_check) {
            clause* cl = m_alloc.mk_clause(c.size(), c.begin(), learned);
            append(*cl, get_status(learned));
        }
    }
    void drat::add(literal_vector const& lits, svector<premise> const& premises) {
        if (m_check) {
            switch (lits.size()) {
            case 0: add(); break;
            case 1: append(lits[0], status::external); break;
            default: {
                clause* c = m_alloc.mk_clause(lits.size(), lits.c_ptr(), true);
                append(*c, status::external);
                break;
            }
            }
        }                        
    }
    void drat::add(literal_vector const& c) {
        if (m_out) dump(c.size(), c.begin(), status::learned);
        if (m_bout) bdump(c.size(), c.begin(), status::learned);
        if (m_check) {
            for (literal lit : c) declare(lit);
            switch (c.size()) {
            case 0: add(); break;
            case 1: append(c[0], status::learned); break;
            default: {
                verify(c.size(), c.begin());
                clause* cl = m_alloc.mk_clause(c.size(), c.c_ptr(), true);
                append(*cl, status::external);                
                break;
            }
            }
        }
    }

    void drat::del(literal l) {
        if (m_out) dump(1, &l, status::deleted);
        if (m_bout) bdump(1, &l, status::deleted);
        if (m_check_unsat) append(l, status::deleted);
    }

    void drat::del(literal l1, literal l2) {
        literal ls[2] = {l1, l2};
        SASSERT(!(l1 == literal(13923, false) && l2 == literal(14020, true)));
        if (m_out) dump(2, ls, status::deleted);
        if (m_bout) bdump(2, ls, status::deleted);
        if (m_check) append(l1, l2, status::deleted);
    }

    void drat::del(clause& c) {

#if 0
        // check_duplicates:
        for (literal lit : c) {
            VERIFY(!m_seen[lit.index()]);
            m_seen[lit.index()] = true;
        }
        for (literal lit : c) {
            m_seen[lit.index()] = false;
        }
#endif

        //SASSERT(!(c.size() == 2 && c[0] == literal(13923, false) && c[1] == literal(14020, true)));
        if (m_out) dump(c.size(), c.begin(), status::deleted);
        if (m_bout) bdump(c.size(), c.begin(), status::deleted);
        if (m_check) {
            clause* c1 = m_alloc.mk_clause(c.size(), c.begin(), c.is_learned()); 
            append(*c1, status::deleted);
        }
    }
    
    void drat::check_model(model const& m) {        
    }

}
