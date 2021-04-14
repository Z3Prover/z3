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
    drat::drat(solver& s) :
        s(s),
        m_out(nullptr),
        m_bout(nullptr),
        m_inconsistent(false),
        m_check_unsat(false),
        m_check_sat(false),
        m_check(false),
        m_activity(false)
    {
        if (s.get_config().m_drat && s.get_config().m_drat_file.is_non_empty_string()) {
            auto mode = s.get_config().m_drat_binary ? (std::ios_base::binary | std::ios_base::out | std::ios_base::trunc) : std::ios_base::out;
            m_out = alloc(std::ofstream, s.get_config().m_drat_file.str(), mode);
            if (s.get_config().m_drat_binary) {
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
        m_check_unsat = s.get_config().m_drat_check_unsat;
        m_check_sat = s.get_config().m_drat_check_sat;
        m_check = m_check_unsat || m_check_sat;
        m_activity = s.get_config().m_drat_activity;
    }

    std::ostream& drat::pp(std::ostream& out, status st) const {
        if (st.is_redundant())
            out << "l";
        else if (st.is_deleted())
            out << "d";
        else if (st.is_asserted())
            out << "a";
        else if (st.is_input())
            out << "i";

        if (!st.is_sat())
            out << " " << m_theory[st.get_th()];
        return out;
    }

    void drat::dump(unsigned n, literal const* c, status st) {
        if (st.is_asserted() && !s.m_ext)
            return;
        if (m_activity && ((m_stats.m_num_add % 1000) == 0))
            dump_activity();
        
        char buffer[10000];
        char digits[20];     // enough for storing unsigned
        char* lastd = digits + sizeof(digits);

        unsigned len = 0;

        if (st.is_deleted()) {
            buffer[len++] = 'd';
            buffer[len++] = ' ';
        }
        else if (st.is_input()) {
            buffer[len++] = 'i';
            buffer[len++] = ' ';
        }
        else if (!st.is_sat()) {
            if (st.is_redundant()) {
                buffer[len++] = 'r';
                buffer[len++] = ' ';
            }
            else if (st.is_asserted()) {
                buffer[len++] = 'a';
                buffer[len++] = ' ';
            }
        }

        if (!st.is_sat()) {
            for (char ch : m_theory[st.get_th()])
                buffer[len++] = ch;
            buffer[len++] = ' ';
        }
        for (unsigned i = 0; i < n; ++i) {
            literal lit = c[i];
            unsigned v = lit.var();
            if (lit.sign()) buffer[len++] = '-';
            char* d = lastd;
            SASSERT(v > 0);
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

    void drat::dump_activity() {
        (*m_out) << "c activity ";
        for (unsigned v = 0; v < s.num_vars(); ++v) {
            (*m_out) << s.m_activity[v] << " ";
        }
        (*m_out) << "\n";
    }

    void drat::bdump(unsigned n, literal const* c, status st) {
        unsigned char ch = 0;
        if (st.is_redundant())
            ch = 'a';
        else if (st.is_deleted())
            ch = 'd';
        else return;
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
            } while (v);
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
        pp(out, st) << " ";
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
        TRACE("sat_drat", pp(tout, st) << " " << l << "\n";);

        declare(l);
        IF_VERBOSE(20, trace(verbose_stream(), 1, &l, st););
        if (st.is_redundant() && st.is_sat()) {
            verify(1, &l);
        }
        if (st.is_deleted()) {
            return;
        }
        if (m_check_unsat) {
            assign_propagate(l);
        }

        m_units.push_back(l);
    }

    void drat::append(literal l1, literal l2, status st) {
        TRACE("sat_drat", pp(tout, st) << " " << l1 << " " << l2 << "\n";);
        declare(l1);
        declare(l2);
        literal lits[2] = { l1, l2 };

        IF_VERBOSE(20, trace(verbose_stream(), 2, lits, st););
        if (st.is_deleted()) {
            // noop
            // don't record binary as deleted.
        }
        else {
            if (st.is_redundant() && st.is_sat()) {
                verify(2, lits);
            }
            clause* c = m_alloc.mk_clause(2, lits, st.is_redundant());
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

    void drat::bool_def(bool_var v, unsigned n) {
        if (m_out)
            (*m_out) << "b " << v << " " << n << " 0\n";
    }

    void drat::def_begin(char id, unsigned n, std::string const& name) {
        if (m_out) 
            (*m_out) << id << " " << n << " " << name;
    }

    void drat::def_add_arg(unsigned arg) {
        if (m_out)
            (*m_out) << " " << arg;
    }

    void drat::def_end() {
        if (m_out)
            (*m_out) << " 0\n";
    }

    void drat::log_adhoc(std::function<void(std::ostream&)>& fn) {
        if (m_out)
            fn(*m_out);
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
        TRACE("sat_drat", pp(tout, st) << " " << c << "\n";);
        for (literal lit : c) declare(lit);
        unsigned n = c.size();
        IF_VERBOSE(20, trace(verbose_stream(), n, c.begin(), st););

        if (st.is_redundant() && st.is_sat()) {
            verify(c);
        }

        m_status.push_back(st);
        m_proof.push_back(&c);
        if (st.is_deleted()) {
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

    bool drat::is_drup(unsigned n, literal const* c, literal_vector& units) {
        if (m_inconsistent) 
            return true;
        if (n == 0)
            return false;

        unsigned num_units = m_units.size();
        for (unsigned i = 0; !m_inconsistent && i < n; ++i) {
            declare(c[i]);
            assign_propagate(~c[i]);
        }

        for (unsigned i = num_units; i < m_units.size(); ++i) {
            m_assignment[m_units[i].var()] = l_undef;
        }
        units.append(m_units.size() - num_units, m_units.data() + num_units);
        m_units.shrink(num_units);
        bool ok = m_inconsistent;
        m_inconsistent = false;
        return ok;
    }

    bool drat::is_drup(unsigned n, literal const* c) {
        if (m_inconsistent) 
            return true;
        if (n == 0)
            return false;
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
            for (auto& b : bin) {
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
        m_inconsistent = false;
        return ok;
    }

    bool drat::is_drat(unsigned n, literal const* c) {
        return false;
        if (m_inconsistent || n == 0) 
            return true;
        for (unsigned i = 0; i < n; ++i) 
            if (is_drat(n, c, i)) 
                return true;
        return false;
    }

    void drat::validate_propagation() const {
        for (unsigned i = 0; i < m_proof.size(); ++i) {
            status st = m_status[i];
            if (m_proof[i] && m_proof[i]->size() > 1 && !st.is_deleted()) {
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
            if (m_proof[i] && m_proof[i]->size() > 1 && st.is_asserted()) {
                clause& c = *m_proof[i];
                unsigned j = 0;
                for (; j < c.size() && c[j] != ~l; ++j) {}
                if (j != c.size()) {
                    lits.append(j, c.begin());
                    lits.append(c.size() - j - 1, c.begin() + j + 1);
                    if (!is_drup(lits.size(), lits.data()))
                        return false;
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
        if (is_drup(n, c)) {
            ++m_stats.m_num_drup;
            return;
        }
        if (is_drat(n, c)) {
            ++m_stats.m_num_drat;
            return;
        }

        literal_vector lits(n, c);
        IF_VERBOSE(0, verbose_stream() << "Verification of " << lits << " failed\n");
        // s.display(std::cout);
        std::string line;
        std::getline(std::cin, line);
        exit(0);
#if 0
        SASSERT(false);
        INVOKE_DEBUGGER();
        exit(0);
        UNREACHABLE();
        //display(std::cout);
        TRACE("sat_drat",
              tout << literal_vector(n, c) << "\n";
              display(tout);
              s.display(tout););
        UNREACHABLE();
#endif
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
                if (st.is_deleted()) {
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
            if (!m_status[i].is_deleted() && c) {
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
                pp(out, m_status[i]) << " " << i << ": " << *c << "\n";
            }
        }
        for (unsigned i = 0; i < m_assignment.size(); ++i) {
            watch const& w1 = m_watches[2 * i];
            watch const& w2 = m_watches[2 * i + 1];
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

    status drat::get_status(bool learned) const {
        if (learned || s.m_searching)
            return status::redundant();
        return status::asserted();
    }

    void drat::add() {
        ++m_stats.m_num_add;
        if (m_out) (*m_out) << "0\n";
        if (m_bout) bdump(0, nullptr, status::redundant());
        if (m_check_unsat) {
            verify(0, nullptr);
            SASSERT(m_inconsistent);
        }
    }
    void drat::add(literal l, bool learned) {
        ++m_stats.m_num_add;
        status st = get_status(learned);
        if (m_out) dump(1, &l, st);
        if (m_bout) bdump(1, &l, st);
        if (m_check) append(l, st);
    }
    void drat::add(literal l1, literal l2, status st) {
        if (st.is_deleted())
            ++m_stats.m_num_del;
        else
            ++m_stats.m_num_add;
        literal ls[2] = { l1, l2 };
        if (m_out) dump(2, ls, st);
        if (m_bout) bdump(2, ls, st);
        if (m_check) append(l1, l2, st);
    }
    void drat::add(clause& c, status st) {
        if (st.is_deleted())
            ++m_stats.m_num_del;
        else
            ++m_stats.m_num_add;
        if (m_out) dump(c.size(), c.begin(), st);
        if (m_bout) bdump(c.size(), c.begin(), st);
        if (m_check) {
            clause* cl = m_alloc.mk_clause(c.size(), c.begin(), st.is_redundant());
            append(*cl, st);
        }
    }
    void drat::add(literal_vector const& lits, status st) {
        add(lits.size(), lits.data(), st);
    }

    void drat::add(unsigned sz, literal const* lits, status st) {
        if (st.is_deleted())
            ++m_stats.m_num_del;
        else
            ++m_stats.m_num_add;
        if (m_check) {
            switch (sz) {
            case 0: add(); break;
            case 1: append(lits[0], st); break;
            default: {
                clause* c = m_alloc.mk_clause(sz, lits, st.is_redundant());
                append(*c, st);
                break;
            }
            }
        }
        if (m_out)
            dump(sz, lits, st);
    }

    void drat::add(literal_vector const& c) {
        ++m_stats.m_num_add;
        if (m_out) dump(c.size(), c.begin(), status::redundant());
        if (m_bout) bdump(c.size(), c.begin(), status::redundant());
        if (m_check) {
            for (literal lit : c) declare(lit);
            switch (c.size()) {
            case 0: add(); break;
            case 1: append(c[0], status::redundant()); break;
            default: {
                verify(c.size(), c.begin());
                clause* cl = m_alloc.mk_clause(c.size(), c.data(), true);
                append(*cl, status::redundant());
                break;
            }
            }
        }
    }

    void drat::del(literal l) {
        ++m_stats.m_num_del;
        if (m_out) dump(1, &l, status::deleted());
        if (m_bout) bdump(1, &l, status::deleted());
        if (m_check_unsat) append(l, status::deleted());
    }

    void drat::del(literal l1, literal l2) {
        ++m_stats.m_num_del;
        literal ls[2] = { l1, l2 };
        if (m_out) dump(2, ls, status::deleted());
        if (m_bout) bdump(2, ls, status::deleted());
        if (m_check) append(l1, l2, status::deleted());
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
        ++m_stats.m_num_del;
        if (m_out) dump(c.size(), c.begin(), status::deleted());
        if (m_bout) bdump(c.size(), c.begin(), status::deleted());
        if (m_check) {
            clause* c1 = m_alloc.mk_clause(c.size(), c.begin(), c.is_learned());
            append(*c1, status::deleted());
        }
    }

    void drat::del(literal_vector const& c) {
        ++m_stats.m_num_del;
        if (m_out) dump(c.size(), c.begin(), status::deleted());
        if (m_bout) bdump(c.size(), c.begin(), status::deleted());
        if (m_check) {
            clause* c1 = m_alloc.mk_clause(c.size(), c.begin(), true);
            append(*c1, status::deleted());
        }
    }

    void drat::check_model(model const& m) {
    }

    void drat::collect_statistics(statistics& st) const {
        st.update("num-drup", m_stats.m_num_drup);
        st.update("num-drat", m_stats.m_num_drat);
        st.update("num-add", m_stats.m_num_add);
        st.update("num-del", m_stats.m_num_del);
    }


    std::ostream& operator<<(std::ostream& out, sat::status const& st) {
        std::function<symbol(int)> th = [&](int id) { return symbol(id); };
        return out << sat::status_pp(st, th);
    }
    
    std::ostream& operator<<(std::ostream& out, sat::status_pp const& p) {
        auto st = p.st;
        if (st.is_deleted())
            out << "d";
        else if (st.is_input())
            out << "i";
        else if (st.is_asserted())
            out << "a";
        else if (st.is_redundant() && !st.is_sat())
            out << "r";
        if (!st.is_sat())
            out << " " << p.th(st.get_th());
        return out;
    }    

}
