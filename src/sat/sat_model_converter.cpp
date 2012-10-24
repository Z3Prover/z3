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
#include"sat_model_converter.h"
#include"sat_clause.h"
#include"trace.h"

namespace sat {

    model_converter::model_converter() {
    }

    model_converter::~model_converter() {
        reset();
    }

    void model_converter::reset() {
        m_entries.finalize();
    }
    
    void model_converter::operator()(model & m) const {
        vector<entry>::const_iterator begin = m_entries.begin();
        vector<entry>::const_iterator it    = m_entries.end();
        while (it != begin) {
            --it;
            SASSERT(it->get_kind() != ELIM_VAR || m[it->var()] == l_undef);
            // if it->get_kind() == BLOCK_LIT, then it might be the case that m[it->var()] != l_undef,
            // and the following procedure flips its value.
            bool sat = false;
            bool var_sign;
            literal_vector::const_iterator it2  = it->m_clauses.begin();
            literal_vector::const_iterator end2 = it->m_clauses.end();
            for (; it2 != end2; ++it2) {
                literal l  = *it2;
                if (l == null_literal) {
                    // end of clause
                    if (!sat) {
                        m[it->var()] = var_sign ? l_false : l_true;
                        break;
                    }
                    sat = false;
                    continue;
                }
                if (sat)
                    continue;
                bool sign  = l.sign();
                bool_var v = l.var();
                if (v == it->var())
                    var_sign = sign;
                if (value_at(l, m) == l_true)
                    sat = true;
                else if (!sat && v != it->var() && m[v] == l_undef) {
                    // clause can be satisfied by assigning v.
                    m[v] = sign ? l_false : l_true;
                    sat = true;
                }
            }
            DEBUG_CODE({
                // all clauses must be satisfied
                bool sat = false;
                it2 = it->m_clauses.begin();
                for (; it2 != end2; ++it2) {
                    literal l = *it2;
                    if (l == null_literal) {
                        SASSERT(sat);
                        sat = false;
                        continue;
                    }
                    if (sat)
                        continue;
                    if (value_at(l, m) == l_true)
                        sat = true;
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
        return e;
    }

    void model_converter::insert(entry & e, clause const & c) {
        SASSERT(c.contains(e.var()));
        SASSERT(m_entries.begin() <= &e);
        SASSERT(&e < m_entries.end());
        unsigned sz = c.size();
        for (unsigned i = 0; i < sz; i++) {
            e.m_clauses.push_back(c[i]);
        }
        e.m_clauses.push_back(null_literal);
        TRACE("sat_mc_bug", tout << "adding: " << c << "\n";);
    }

    void model_converter::insert(entry & e, literal l1, literal l2) {
        SASSERT(l1.var() == e.var() || l2.var() == e.var());
        SASSERT(m_entries.begin() <= &e);
        SASSERT(&e < m_entries.end());
        e.m_clauses.push_back(l1);
        e.m_clauses.push_back(l2);
        e.m_clauses.push_back(null_literal);
        TRACE("sat_mc_bug", tout << "adding (binary): " << l1 << " " << l2 << "\n";);
    }

    void model_converter::insert(entry & e, clause_wrapper const & c) {
        SASSERT(c.contains(e.var()));
        SASSERT(m_entries.begin() <= &e);
        SASSERT(&e < m_entries.end());
        unsigned sz = c.size();
        for (unsigned i = 0; i < sz; i++)
            e.m_clauses.push_back(c[i]);
        e.m_clauses.push_back(null_literal);
        TRACE("sat_mc_bug", tout << "adding (wrapper): "; for (unsigned i = 0; i < c.size(); i++) tout << c[i] << " "; tout << "\n";);
    }

    bool model_converter::check_invariant(unsigned num_vars) const {
        // After a variable v occurs in an entry n and the entry has kind ELIM_VAR,
        // then the variable must not occur in any other entry occurring after it.
        vector<entry>::const_iterator it  = m_entries.begin();
        vector<entry>::const_iterator end = m_entries.end();
        for (; it != end; ++it) {
            SASSERT(it->var() < num_vars);
            if (it->get_kind() == ELIM_VAR) {
                svector<entry>::const_iterator it2 = it;
                it2++;
                for (; it2 != end; ++it2) {
                    SASSERT(it2->var() != it->var());
                    literal_vector::const_iterator it3  = it2->m_clauses.begin();
                    literal_vector::const_iterator end3 = it2->m_clauses.end();
                    for (; it3 != end3; ++it3) {
                        CTRACE("sat_model_converter", it3->var() == it->var(), tout << "var: " << it->var() << "\n"; display(tout););
                        SASSERT(it3->var() != it->var());
                        SASSERT(*it3 == null_literal || it3->var() < num_vars);
                    }
                }
            }
        }
        return true;
    }

    void model_converter::display(std::ostream & out) const {
        out << "(sat::model-converter";
        vector<entry>::const_iterator it  = m_entries.begin();
        vector<entry>::const_iterator end = m_entries.end();
        for (; it != end; ++it) {
            out << "\n  (" << (it->get_kind() == ELIM_VAR ? "elim" : "blocked") << " " << it->var();
            bool start = true;
            literal_vector::const_iterator it2  = it->m_clauses.begin();
            literal_vector::const_iterator end2 = it->m_clauses.end();
            for (; it2 != end2; ++it2) {
                if (start) {
                    out << "\n    (";
                    start = false;
                }
                else {
                    if (*it2 != null_literal)
                        out << " ";
                }
                if (*it2 == null_literal) {
                    out << ")";
                    start = true;
                    continue;
                }
                out << *it2;
            }
            out << ")";
        }    
        out << ")\n";
    }

    void model_converter::copy(model_converter const & src) {
        vector<entry>::const_iterator it  = src.m_entries.begin();
        vector<entry>::const_iterator end = src.m_entries.end();
        for (; it != end; ++it)
            m_entries.push_back(*it);
    }

    void model_converter::collect_vars(bool_var_set & s) const {
        vector<entry>::const_iterator it  = m_entries.begin();
        vector<entry>::const_iterator end = m_entries.end();
        for (; it != end; ++it) {
            s.insert(it->m_var);
        }
    }

};
