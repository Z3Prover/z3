/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   sat_xor_finder.cpp

  Abstract:
   
    xor finder

  Author:

    Nikolaj Bjorner 2020-01-02

  Notes:
  

  --*/

#include "sat/sat_xor_finder.h"
#include "sat/sat_solver.h"

namespace sat {


    void xor_finder::operator()(clause_vector& clauses) {
        m_removed_clauses.reset();
        unsigned max_size = m_max_xor_size;
        // we better have enough bits in the combination mask to 
        // handle clauses up to max_size.
        // max_size = 5 -> 32 bits
        // max_size = 6 -> 64 bits
        SASSERT(sizeof(m_combination)*8 <= (1ull << static_cast<uint64_t>(max_size)));
        init_clause_filter();
        m_var_position.resize(s.num_vars());
        for (clause* cp : clauses) {
            cp->unmark_used();
        }
        for (; max_size > 2; --max_size) {
            for (clause* cp : clauses) {
                clause& c = *cp;
                if (c.size() == max_size && !c.was_removed() && !c.is_learned() && !c.was_used()) {
                    extract_xor(c);
                }
            }
        }
        m_clause_filters.clear();
        
        for (clause* cp : clauses) cp->unmark_used();
        for (clause* cp : m_removed_clauses) cp->mark_used();
        std::function<bool(clause*)> not_used = [](clause* cp) { return !cp->was_used(); };
        clauses.filter_update(not_used);
    }

    void xor_finder::extract_xor(clause& c) {
        SASSERT(c.size() > 2);
        unsigned filter = get_clause_filter(c);
        s.init_visited();
        TRACE("sat_xor", tout << c << "\n";);
        bool parity = false;
        unsigned mask = 0, i = 0;        
        for (literal l : c) {
            m_var_position[l.var()] = i;
            s.mark_visited(l.var());
            parity ^= !l.sign();
            mask |= (!l.sign() << (i++)); 
        }
        // parity is number of true literals in clause.
        m_clauses_to_remove.reset();
        m_clauses_to_remove.push_back(&c);
        m_clause.resize(c.size());
        m_combination = 0;
        set_combination(mask);
        c.mark_used();
        for (literal l : c) {
            for (auto const& cf : m_clause_filters[l.var()]) {                
                if ((filter == (filter | cf.m_filter)) && 
                    !cf.m_clause->was_used() &&
                    extract_xor(parity, c, *cf.m_clause)) {
                    add_xor(parity, c);
                    return;
                }
            }
            // loop over binary clauses in watch list
            for (watched const & w : s.get_wlist(l)) {
                if (w.is_binary_clause() && s.is_visited(w.get_literal().var()) && w.get_literal().index() < l.index()) {
                    if (extract_xor(parity, c, ~l, w.get_literal())) {
                        add_xor(parity, c);
                        return;
                    }
                }
            }
            l.neg();
            for (watched const & w : s.get_wlist(l)) {
                if (w.is_binary_clause() && s.is_visited(w.get_literal().var()) && w.get_literal().index() < l.index()) {
                    if (extract_xor(parity, c, ~l, w.get_literal())) {
                        add_xor(parity, c);
                        return;
                    }
                }
            }
        }
    }

    void xor_finder::set_combination(unsigned mask) { 
        m_combination |= (1 << mask); 
    }


    void xor_finder::add_xor(bool parity, clause& c) {
        DEBUG_CODE(for (clause* cp : m_clauses_to_remove) VERIFY(cp->was_used()););
        m_removed_clauses.append(m_clauses_to_remove);
        literal_vector lits;
        for (literal l : c) {
            lits.push_back(literal(l.var(), false));
            s.set_external(l.var());
        }
        if (parity == (lits.size() % 2 == 0)) lits[0].neg();
        TRACE("sat_xor", tout << parity << ": " << lits << "\n";);
        m_on_xor(lits);
    }

    bool xor_finder::extract_xor(bool parity, clause& c, literal l1, literal l2) {
        SASSERT(s.is_visited(l1.var()));
        SASSERT(s.is_visited(l2.var()));
        m_missing.reset();
        unsigned mask = 0;
        for (unsigned i = 0; i < c.size(); ++i) {
            if (c[i].var() == l1.var()) {
                mask |= (!l1.sign() << i);
            }
            else if (c[i].var() == l2.var()) {
                mask |= (!l2.sign() << i);
            }
            else {
                m_missing.push_back(i);
            }
        }
        TRACE("sat_xor", tout << l1 << " " << l2 << "\n";);
        return update_combinations(c, parity, mask);
    }

    bool xor_finder::extract_xor(bool parity, clause& c, clause& c2) {
        bool parity2 = false;
        for (literal l : c2) {            
            if (!s.is_visited(l.var())) return false;
            parity2 ^= !l.sign();
        }
        if (c2.size() == c.size() && parity2 != parity) {
            return false;
        }
        if (c2.size() == c.size()) {
            m_clauses_to_remove.push_back(&c2);
            c2.mark_used();
        }
        TRACE("sat_xor", tout << c2 << "\n";);
        // insert missing
        unsigned mask = 0;
        m_missing.reset();
        SASSERT(c2.size() <= c.size());
        for (unsigned i = 0; i < c.size(); ++i) {
            m_clause[i] = null_literal;
        }
        for (literal l : c2) {
            unsigned pos = m_var_position[l.var()];
            m_clause[pos] = l;
        }
        for (unsigned j = 0; j < c.size(); ++j) {
            literal lit = m_clause[j];
            if (lit == null_literal) {
                m_missing.push_back(j);
            }
            else {
                mask |= (!m_clause[j].sign() << j);
            }
        }                
        return update_combinations(c, parity, mask);
    }

    bool xor_finder::update_combinations(clause& c, bool parity, unsigned mask) {
        unsigned num_missing = m_missing.size();
        for (unsigned k = 0; k < (1ul << num_missing); ++k) {
            unsigned mask2 = mask;
            for (unsigned i = 0; i < num_missing; ++i) {
                if ((k & (1 << i)) != 0) {
                    mask2 |= 1ul << m_missing[i];
                }
            }
            set_combination(mask2);
        }
        // return true if xor clause is covered.
        unsigned sz = c.size();
        for (unsigned i = 0; i < (1ul << sz); ++i) {     
            TRACE("sat_xor", tout << i << ": " << parity << " " << m_parity[sz][i] << " " << get_combination(i) << "\n";);
            if (parity == m_parity[sz][i] && !get_combination(i)) {
                return false;
            }
        }
        return true;
    }

    void xor_finder::init_parity() {
        for (unsigned i = m_parity.size(); i <= m_max_xor_size; ++i) {
            bool_vector bv;
            for (unsigned j = 0; j < (1ul << i); ++j) {
                bool parity = false;
                for (unsigned k = 0; k < i; ++k) {
                    parity ^= ((j & (1 << k)) != 0);
                }
                bv.push_back(parity);
            }
            m_parity.push_back(bv);
        }
    }

    void xor_finder::init_clause_filter() {
        m_clause_filters.reset();
        m_clause_filters.resize(s.num_vars());
        init_clause_filter(s.m_clauses);
        init_clause_filter(s.m_learned);
    }

    void xor_finder::init_clause_filter(clause_vector& clauses) {
        for (clause* cp : clauses) {
            clause& c = *cp;
            if (c.size() <= m_max_xor_size && s.all_distinct(c)) {
                clause_filter cf(get_clause_filter(c), cp);
                for (literal l : c) {
                    m_clause_filters[l.var()].push_back(cf);
                }            
            }
        }
    }

    unsigned xor_finder::get_clause_filter(clause& c) {
        unsigned filter = 0;
        for (literal l : c) {
            filter |= 1 << ((l.var() % 32));
        }
        return filter;
    }


}
