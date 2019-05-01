/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_model_converter.cpp

Abstract:

    Low level model converter for SAT solver.

Author:

    Leonardo de Moura (leonardo) 2011-05-26.

Revision History:

--*/
#include "sat/sat_model_converter.h"
#include "sat/sat_clause.h"
#include "sat/sat_solver.h"
#include "util/trace.h"

namespace sat {

    model_converter::model_converter(): m_solver(nullptr) {
    }

    model_converter::~model_converter() {
        reset();
    }

    void model_converter::reset() {
        m_entries.finalize();
    }

    model_converter& model_converter::operator=(model_converter const& other) {
        copy(other);
        return *this;
    }

    bool model_converter::legal_to_flip(bool_var v) const {
        // std::cout << "check " << v << " " << m_solver << "\n";
        if (m_solver && m_solver->is_assumption(v)) {
            std::cout << "flipping assumption v" << v << "\n";
            UNREACHABLE();
            throw solver_exception("flipping assumption");
        }
        if (m_solver && m_solver->is_external(v) && m_solver->is_incremental()) {
            std::cout << "flipping external v" << v << "\n";
            UNREACHABLE();
            throw solver_exception("flipping external");
        }
        return !m_solver || !m_solver->is_assumption(v);
    }


    void model_converter::process_stack(model & m, literal_vector const& c, elim_stackv const& stack) const {
        SASSERT(!stack.empty());
        unsigned sz = stack.size();
        for (unsigned i = sz; i-- > 0; ) {
            unsigned csz = stack[i].first;
            literal lit = stack[i].second;
            bool sat = false;
            for (unsigned j = 0; !sat && j < csz; ++j) {
                sat = value_at(c[j], m) == l_true;
            }
            if (!sat) {
                VERIFY(legal_to_flip(lit.var()));
                m[lit.var()] = lit.sign() ? l_false : l_true;
            }
        }
    }
    
    void model_converter::operator()(model & m) const {
        vector<entry>::const_iterator begin = m_entries.begin();
        vector<entry>::const_iterator it    = m_entries.end();
        bool first =  false; 
        //SASSERT(!m_solver || m_solver->check_clauses(m));
        while (it != begin) {
            --it;
            bool_var v0 = it->var();
            SASSERT(it->get_kind() != ELIM_VAR || v0 == null_bool_var || m[v0] == l_undef);
            // if it->get_kind() == BCE, then it might be the case that m[v] != l_undef,
            // and the following procedure flips its value.
            bool sat = false;
            bool var_sign = false;
            unsigned index = 0;
            literal_vector clause;
            VERIFY(v0 == null_bool_var || legal_to_flip(v0));
            for (literal l : it->m_clauses) {
                if (l == null_literal) {
                    // end of clause
                    if (!sat && it->get_kind() == ATE) {
                        IF_VERBOSE(0, display(verbose_stream() << "violated ate\n", *it) << "\n");
                        IF_VERBOSE(0, for (unsigned v = 0; v < m.size(); ++v) verbose_stream() << v << " := " << m[v] << "\n";);
                        IF_VERBOSE(0, display(verbose_stream()));
                        UNREACHABLE();
                        first = false;
                    }
                    if (!sat && it->get_kind() != ATE && v0 != null_bool_var) {     
                        VERIFY(legal_to_flip(v0));                        
                        m[v0] = var_sign ? l_false : l_true;
                        //IF_VERBOSE(0, verbose_stream() << "assign " << v0 << " "<< m[v0] << "\n");
                    }
                    elim_stack* st = it->m_elim_stack[index];
                    if (st) {
                        process_stack(m, clause, st->stack());
                    }
                    sat = false;
                    if (first && m_solver && !m_solver->check_clauses(m)) {
                        IF_VERBOSE(0, display(verbose_stream() << "after processing stack\n", *it) << "\n");
                        IF_VERBOSE(0, display(verbose_stream()));
                        first = false;
                    }
                    ++index;
                    clause.reset();
                    continue;                    
                }

                clause.push_back(l);
                if (sat)
                    continue;
                bool sign  = l.sign();
                bool_var v = l.var();
                if (v >= m.size()) std::cout << v << " model size: " << m.size() << "\n";
                VERIFY(v < m.size());
                if (v == v0)
                    var_sign = sign;
                if (value_at(l, m) == l_true)
                    sat = true;
                else if (!sat && v != v0 && m[v] == l_undef) {
                    VERIFY(legal_to_flip(v));
                    // clause can be satisfied by assigning v.
                    m[v] = sign ? l_false : l_true;
                    // if (first) std::cout << "set: " << l << "\n";
                    sat = true;
                    if (first && m_solver && !m_solver->check_clauses(m)) {
                        IF_VERBOSE(0, display(verbose_stream() << "after flipping undef\n", *it)  << "\n");
                        first = false;
                    }
                }
            }
            DEBUG_CODE({
                // all clauses must be satisfied
                bool sat = false;
                bool undef = false;
                for (literal const& l : it->m_clauses) {
                    if (l == null_literal) {
                        CTRACE("sat", !sat, 
                               if (m_solver) m_solver->display(tout);
                               display(tout);
                               for (unsigned v = 0; v < m.size(); ++v) tout << v << ": " << m[v] << "\n";
                               for (literal const& l2 : it->m_clauses) {
                                   if (l2 == null_literal) tout << "\n"; else tout << l2 << " ";
                                   if (&l == &l2) break;
                               }
                               );
                        SASSERT(sat || undef);
                        sat = false;
                        undef = false;
                        continue;
                    }
                    if (sat)
                        continue;
                    switch (value_at(l, m)) {
                    case l_undef: undef = true; break;
                    case l_true: sat = true; break;
                    default: break;
                    }
                }
            });
        }
    }

    /**
       \brief Test if after applying the model converter, all eliminated clauses are
       satisfied by m.
    */
    bool model_converter::check_model(model const & m) const {
        bool ok = true;
        vector<entry>::const_iterator begin = m_entries.begin();
        vector<entry>::const_iterator it    = m_entries.end();
        while (it != begin) {
            --it;
            bool sat = false;
            literal_vector::const_iterator it2     = it->m_clauses.begin();
            literal_vector::const_iterator itbegin = it2;
            literal_vector::const_iterator end2    = it->m_clauses.end();
            for (; it2 != end2; ++it2) {
                literal l  = *it2;
                if (l == null_literal) {
                    // end of clause
                    if (!sat) {
                        TRACE("sat_model_bug", tout << "failed eliminated: " << mk_lits_pp(static_cast<unsigned>(it2 - itbegin), itbegin) << "\n";);
                        ok = false;
                    }
                    sat = false;
                    itbegin = it2;
                    itbegin++;
                    continue;
                }
                if (sat)
                    continue;
                if (value_at(l, m) == l_true)
                    sat = true;
            }
        }
        return ok;
    }

    model_converter::entry & model_converter::mk(kind k, bool_var v) {
        m_entries.push_back(entry(k, v));
        entry & e = m_entries.back();
        SASSERT(e.var() == v);
        SASSERT(e.get_kind() == k);
        VERIFY(v == null_bool_var || legal_to_flip(v));
        return e;
    }

    void model_converter::add_ate(clause const& c) {
        if (stackv().empty()) return;
        insert(mk(ATE, null_bool_var), c);
    }

    void model_converter::add_ate(literal_vector const& lits) {
        if (stackv().empty()) return;
        insert(mk(ATE, null_bool_var), lits);
    }

    void model_converter::add_ate(literal l1, literal l2) {
        if (stackv().empty()) return;
        insert(mk(ATE, null_bool_var), l1, l2);
    }

    void model_converter::add_elim_stack(entry & e) {
        e.m_elim_stack.push_back(stackv().empty() ? nullptr : alloc(elim_stack, stackv()));
        // VERIFY(for (auto const& s : stackv()) VERIFY(legal_to_flip(s.second.var())););
        stackv().reset();
    }

    void model_converter::insert(entry & e, clause const & c) {
        SASSERT(c.contains(e.var()));
        SASSERT(m_entries.begin() <= &e);
        SASSERT(&e < m_entries.end());
        for (literal l : c) e.m_clauses.push_back(l);
        e.m_clauses.push_back(null_literal);
        add_elim_stack(e);
        TRACE("sat_mc_bug", tout << "adding: " << c << "\n";);
    }

    void model_converter::insert(entry & e, literal l1, literal l2) {
        SASSERT(l1.var() == e.var() || l2.var() == e.var());
        SASSERT(m_entries.begin() <= &e);
        SASSERT(&e < m_entries.end());
        e.m_clauses.push_back(l1);
        e.m_clauses.push_back(l2);
        e.m_clauses.push_back(null_literal);
        add_elim_stack(e);
        TRACE("sat_mc_bug", tout << "adding (binary): " << l1 << " " << l2 << "\n";);
    }

    void model_converter::insert(entry & e, clause_wrapper const & c) {
        SASSERT(c.contains(e.var()));
        SASSERT(m_entries.begin() <= &e);
        SASSERT(&e < m_entries.end());
        unsigned sz = c.size();
        for (unsigned i = 0; i < sz; ++i) 
            e.m_clauses.push_back(c[i]);
        e.m_clauses.push_back(null_literal);
        add_elim_stack(e);
        // TRACE("sat_mc_bug", tout << "adding (wrapper): "; for (literal l : c) tout << l << " "; tout << "\n";);
    }

    void model_converter::insert(entry & e, literal_vector const& c) {
        SASSERT(e.var() == null_bool_var || c.contains(literal(e.var(), false)) || c.contains(literal(e.var(), true)));
        SASSERT(m_entries.begin() <= &e);
        SASSERT(&e < m_entries.end());
        for (literal l : c) e.m_clauses.push_back(l);
        e.m_clauses.push_back(null_literal);
        add_elim_stack(e);
        TRACE("sat_mc_bug", tout << "adding: " << c << "\n";);
    }


    bool model_converter::check_invariant(unsigned num_vars) const {
        // After a variable v occurs in an entry n and the entry has kind ELIM_VAR,
        // then the variable must not occur in any other entry occurring after it.
        vector<entry>::const_iterator it  = m_entries.begin();
        vector<entry>::const_iterator end = m_entries.end();
        for (; it != end; ++it) {
            SASSERT(it->var() == null_bool_var || it->var() < num_vars);
            if (it->get_kind() == ELIM_VAR) {
                svector<entry>::const_iterator it2 = it;
                it2++;
                for (; it2 != end; ++it2) {
                    SASSERT(it2->var() != it->var());
                    if (it2->var() == it->var()) return false;
                    for (literal l : it2->m_clauses) {
                        CTRACE("sat_model_converter", l.var() == it->var(), tout << "var: " << it->var() << "\n"; display(tout););
                        SASSERT(l.var() != it->var());
                        VERIFY(l == null_literal || l.var() < num_vars);
                        if (it2->var() == it->var()) return false;
                    }
                }
            }
        }
        return true;
    }

    void model_converter::display(std::ostream & out) const {
        out << "(sat::model-converter\n";
        bool first = true;
        for (auto & entry : m_entries) {
            if (first) first = false; else out << "\n";
            display(out, entry);
        }
        out << ")\n";
    }

    std::ostream& model_converter::display(std::ostream& out, entry const& entry) const {
        out << "  (" << entry.get_kind() << " ";
        if (entry.var() != null_bool_var) out << entry.var(); 
        bool start = true;
        unsigned index = 0;
        for (literal l : entry.m_clauses) {
            if (start) {
                out << "\n    (";
                start = false;
            }
            else {
                if (l != null_literal)
                    out << " ";
            }
            if (l == null_literal) {
                out << ")";
                start = true;
                elim_stack* st = entry.m_elim_stack[index];
                if (st) {
                    elim_stackv const& stack = st->stack();
                    unsigned sz = stack.size();
                    for (unsigned i = sz; i-- > 0; ) {
                        out << "\n   " << stack[i].first << " " << stack[i].second;
                    }
                }
                ++index;
                continue;
            }
            out << l;
        }
        out << ")";
        for (literal l : entry.m_clauses) {
            if (l != null_literal && l.var() != null_bool_var) {
                if (false && m_solver && m_solver->was_eliminated(l.var())) out << "\neliminated: " << l;
            }
        }
        return out;
    }

    void model_converter::copy(model_converter const & src) {
        reset();
        m_entries.append(src.m_entries);
    }

    void model_converter::flush(model_converter & src) {
        VERIFY(this != &src);
        m_entries.append(src.m_entries);
        src.m_entries.reset();
    }

    void model_converter::collect_vars(bool_var_set & s) const {
        for (entry const & e : m_entries) s.insert(e.m_var);
    }

    unsigned model_converter::max_var(unsigned min) const {
        unsigned result = min;
        for (entry const& e : m_entries) {
            for (literal l : e.m_clauses) {
                if (l != null_literal) {
                    if (l.var() != null_bool_var && l.var() > result)
                        result = l.var();
                }
            }
        }
        return result;
    }

    void model_converter::swap(bool_var v, unsigned sz, literal_vector& clause) {
        for (unsigned j = 0; j < sz; ++j) {
            if (v == clause[j].var()) {
                std::swap(clause[0], clause[j]);
                return;
            }
        }
        IF_VERBOSE(0, verbose_stream() << "not found: v" << v << " " << clause << "\n";);
        UNREACHABLE();
    }

    void model_converter::expand(literal_vector& update_stack) {
        sat::literal_vector clause;
        for (entry const& e : m_entries) {
            unsigned index = 0;
            clause.reset();
            for (literal l : e.m_clauses) {
                if (l == null_literal) {
                    elim_stack* st = e.m_elim_stack[index];                    
                    if (st) {
                        // clause sizes increase, so we can always swap
                        // the blocked literal to the front from the prefix.
                        for (auto const& p : st->stack()) {
                            unsigned csz = p.first;
                            literal lit = p.second;
                            swap(lit.var(), csz, clause);
                            update_stack.append(csz, clause.c_ptr());
                            update_stack.push_back(null_literal);
                        }
                    }
                    if (e.var() != null_bool_var) {
                        swap(e.var(), clause.size(), clause);
                        update_stack.append(clause);
                        update_stack.push_back(null_literal);
                    }
                    clause.reset();
                }
                else {
                    clause.push_back(l);
                }
            }
        }
    }

};
