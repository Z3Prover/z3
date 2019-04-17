/*++
  Copyright (c) 2019 Microsoft Corporation

  Module Name:

     emonomials.cpp

  Abstract:

     table that associate monomials to congruence class representatives modulo a union find structure.

  Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)

  Revision History:

    to replace rooted_mons.h and rooted_mon, rooted_mon_tabled

  --*/

#include "util/lp/emonomials.h"
#include "util/lp/nla_defs.h"

namespace nla {

    void emonomials::inc_canonical() {
        ++m_canonical;
        if (m_canonical == 0) {
            for (auto& svt : m_canonized) {
                svt.m_canonical = 0;
            }
            ++m_canonical;
        }
    }

    void emonomials::inc_visited() const {
        ++m_visited;
        if (m_visited == 0) {
            for (auto& svt : m_canonized) {
                svt.m_visited = 0;
            }
            ++m_visited;
        }
    }

    void emonomials::push() { 
        m_lim.push_back(m_monomials.size());
        m_region.push_scope();
        m_ve.push();
    }

    void emonomials::pop(unsigned n) {
        m_ve.pop(n);
        unsigned old_sz = m_lim[m_lim.size() - n];
        for (unsigned i = m_monomials.size(); i-- > old_sz; ) {
            monomial const& m = m_monomials[i];
            m_var2index[m.var()] = UINT_MAX;
            lpvar last_var = UINT_MAX;
            for (lpvar v : m.vars()) {
                if (v != last_var) {
                    remove_var2monomials(v, i);
                    last_var = v;
                }
            }
        }
        m_monomials.shrink(old_sz);
        m_canonized.shrink(old_sz);
        m_region.pop_scope(n);
        m_lim.shrink(m_lim.size() - n);
    }

    void emonomials::remove_var2monomials(lpvar v, unsigned mIndex) {
        cell*& cur_head = m_use_lists[v].m_head;
        cell*& cur_tail = m_use_lists[v].m_tail;
        cell* old_head = cur_head->m_next;
        if (old_head == cur_head) {
            cur_head = nullptr;
            cur_tail = nullptr;
        }
        else {
            cur_head = old_head;
            cur_tail->m_next = old_head;
        }
    }

    void emonomials::insert_var2monomials(lpvar v, unsigned mIndex) {
        m_use_lists.reserve(v + 1);
        cell*& cur_head = m_use_lists[v].m_head;
        cell*& cur_tail = m_use_lists[v].m_tail;
        cell* new_head = new (m_region) cell(mIndex, cur_head);
        cur_head = new_head;
        if (!cur_tail) cur_tail = new_head;
        cur_tail->m_next = new_head;
    }

    void emonomials::merge_var2monomials(lpvar root, lpvar other) {
        if (root == other) return;
        m_use_lists.reserve(std::max(root, other) + 1);
        cell*& root_head = m_use_lists[root].m_head;
        cell*& root_tail = m_use_lists[root].m_tail;
        cell* other_head = m_use_lists[other].m_head;
        cell* other_tail = m_use_lists[other].m_tail;
        if (root_head == nullptr) {
            root_head = other_head;
            root_tail = other_tail;
        }
        else if (other_head) {
            // other_head -> other_tail -> root_head --> root_tail -> other_head.
            root_tail->m_next = other_head;
            other_tail->m_next = root_head;
            root_head = other_head;
        }
        else {
            // other_head = other_tail = nullptr
        }
    }

    void emonomials::unmerge_var2monomials(lpvar root, lpvar other) {
        if (root == other) return;
        cell*& root_head = m_use_lists[root].m_head;
        cell*& root_tail = m_use_lists[root].m_tail;
        cell* other_head = m_use_lists[other].m_head;
        cell* other_tail = m_use_lists[other].m_tail;
        if (other_head == nullptr) {
            // no-op
        }
        else if (root_tail == other_tail) {
            root_head = nullptr;
            root_tail = nullptr;
        }
        else {
            root_head = other_tail->m_next;
            root_tail->m_next = root_head;
            other_tail->m_next = other_head;
        }
    }

    emonomials::cell* emonomials::head(lpvar v) const {
        v = m_ve.find(v).var();
        m_use_lists.reserve(v + 1);
        return m_use_lists[v].m_head;
    }

    void emonomials::set_visited(monomial const& m) const {
        m_canonized[m_var2index[m.var()]].m_visited = m_visited;
    }

    bool emonomials::is_visited(monomial const& m) const {
        return m_visited == m_canonized[m_var2index[m.var()]].m_visited;
    }


    /**
       \brief insert a new monomial.

       Assume that the variables are canonical, that is, not equal in current
       context so another variable. To support equal in current context we
       could track sign information in monomials, or ensure that insert_var2monomials 
       works on the equivalence class roots.
     */
    void emonomials::add(lpvar v, unsigned sz, lpvar const* vs) {
        unsigned idx = m_monomials.size();
        m_monomials.push_back(monomial(v, sz, vs));
        m_canonized.push_back(signed_vars_ts());
        lpvar last_var = UINT_MAX;
        for (unsigned i = 0; i < sz; ++i) {
            lpvar w = vs[i];
            SASSERT(m_ve.is_root(w));
            if (w != last_var) {
                insert_var2monomials(w, idx);
                last_var = w; 
            }
        }
        SASSERT(m_ve.is_root(v));
        m_var2index.setx(v, idx, UINT_MAX);
    }

    signed_vars const& emonomials::canonize(monomial const& mon) const {
        unsigned index = m_var2index[mon.var()];
        if (m_canonized[index].m_canonical != m_canonical) {        
            m_vars.reset();
            bool sign = false;
            for (lpvar v : mon) {
                signed_var sv = m_ve.find(v);
                m_vars.push_back(sv.var());
                sign ^= sv.sign();
            }
            m_canonized[index].set_vars(m_vars.size(), m_vars.c_ptr());
            m_canonized[index].set_sign(sign);
            m_canonized[index].set_var(mon.var());
            m_canonized[index].m_canonical = m_canonical;
        }
        return m_canonized[index];
    }

    bool emonomials::canonize_divides(monomial const& m1, monomial const& m2) const {
        if (m1.size() > m2.size()) return false;
        signed_vars const& s1 = canonize(m1);
        signed_vars const& s2 = canonize(m2);
        unsigned sz1 = s1.size(), sz2 = s2.size();
        unsigned i = 0, j = 0;
        while (true) {
            if (i == sz1) {
                return true;
            }
            else if (j == sz2) {
                return false;
            }
            else if (s1[i] == s2[j]) {
                ++i; ++j;
            }
            else if (s1[i] < s2[j]) {
                return false;
            }
            else {
                ++j;
            }
        }
    }

    void emonomials::explain_canonized(monomial const& m, lp::explanation& exp) {
        for (lpvar v : m) {
            signed_var w = m_ve.find(v);
            m_ve.explain(signed_var(v, false), w, exp);
        }
    }

    // yes, assume that monomials are non-empty.
    emonomials::pf_iterator::pf_iterator(emonomials const& m, monomial const& mon, bool at_end):
        m(m), m_mon(mon), m_it(iterator(m, m.head(mon[0]), at_end)), m_end(iterator(m, m.head(mon[0]), true)) {
        fast_forward();
    }

    void emonomials::pf_iterator::fast_forward() {
        for (; m_it != m_end; ++m_it) {
            if (m_mon.var() != (*m_it).var() && m.canonize_divides(m_mon, *m_it) && !m.is_visited(*m_it)) {
                m.set_visited(*m_it);
                break;
            }
        }
    }

    void emonomials::merge_eh(signed_var r2, signed_var r1, signed_var v2, signed_var v1) {
        if (!r2.sign() && m_ve.find(~r2) != m_ve.find(r1)) {
            merge_var2monomials(r2.var(), r1.var());
        }        
        inc_canonical();
    }

    void emonomials::after_merge_eh(signed_var r2, signed_var r1, signed_var v2, signed_var v1) {
        // skip
    }

    void emonomials::unmerge_eh(signed_var r2, signed_var r1) {
        if (!r2.sign() && m_ve.find(~r2) != m_ve.find(r1)) {
            unmerge_var2monomials(r2.var(), r1.var());            
        }        
        inc_canonical();
    }

   std::ostream& emonomials::display(std::ostream& out) const {
       out << "monomials\n";
       unsigned idx = 0;
       for (auto const& m : m_monomials) {
           out << (idx++) << ": " << m << "\n";
       }
       out << "use lists\n";
       idx = 0;
       for (auto const& ht : m_use_lists) {
           cell* c = ht.m_head;
           if (c) {
               out << "v" << idx << ": ";
               do {
                   out << c->m_index << " ";
                   c = c->m_next;
               }
               while (c != ht.m_head);
               out << "\n";
           }
           ++idx;
       }
       return out;
   }

}
