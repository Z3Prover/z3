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


    void emonomials::inc_visited() const {
        ++m_visited;
        if (m_visited == 0) {
            for (auto& svt : m_monomials) {
                svt.visited() = 0;
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
            monomial & m = m_monomials[i];
            remove_cg(i, m);
            m_var2index[m.var()] = UINT_MAX;
            lpvar last_var = UINT_MAX;
            for (lpvar v : m.vars()) {
                if (v != last_var) {
                    remove_cell(m_use_lists[v], i);
                    last_var = v;
                }
            }
        }
        m_monomials.shrink(old_sz);
        m_monomials.shrink(old_sz);
        m_region.pop_scope(n);
        m_lim.shrink(m_lim.size() - n);
    }

    void emonomials::remove_cell(head_tail& v, unsigned mIndex) {
        cell*& cur_head = v.m_head;
        cell*& cur_tail = v.m_tail;
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

    void emonomials::insert_cell(head_tail& v, unsigned mIndex) {
        cell*& cur_head = v.m_head;
        cell*& cur_tail = v.m_tail;
        cell* new_head = new (m_region) cell(mIndex, cur_head);
        cur_head = new_head;
        if (!cur_tail) cur_tail = new_head;
        cur_tail->m_next = new_head;
    }

    void emonomials::merge_cells(head_tail& root, head_tail& other) {
        if (&root == &other) return;
        cell*& root_head = root.m_head;
        cell*& root_tail = root.m_tail;
        cell* other_head = other.m_head;
        cell* other_tail = other.m_tail;
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

    void emonomials::unmerge_cells(head_tail& root, head_tail& other) {
        if (&root == &other) return;
        cell*& root_head = root.m_head;
        cell*& root_tail = root.m_tail;
        cell* other_head = other.m_head;
        cell* other_tail = other.m_tail;
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

    monomial const* emonomials::find_canonical(svector<lpvar> const& vars) const {
        SASSERT(m_ve.is_root(vars));
        // find a unique key for dummy monomial
        lpvar v = m_var2index.size();
        for (unsigned i = 0; i < m_var2index.size(); ++i) {
            if (m_var2index[i] == UINT_MAX) {
                v = i;
                break;
            }
        }
        unsigned idx = m_monomials.size();
        m_monomials.push_back(monomial(v, vars, idx));
        m_var2index.setx(v, idx, UINT_MAX);
        do_canonize(m_monomials[idx]);
        monomial const* result = nullptr;
        lpvar w; 
        if (m_cg_table.find(v, w)) {
            SASSERT(w != v);
            result = &m_monomials[m_var2index[w]];
        }
        m_var2index[v] = UINT_MAX;
        m_monomials.pop_back();
        return result;
    }


    void emonomials::remove_cg(lpvar v) {
        cell* c = m_use_lists[v].m_head;
        if (c == nullptr) {
            return;
        }
        cell* first = c;
        inc_visited();
        do {
            unsigned idx = c->m_index;
            c = c->m_next;
            monomial & m = m_monomials[idx];
            if (!is_visited(m)) {
                set_visited(m);
                remove_cg(idx, m);
            }
        }
        while (c != first);
    }

    void emonomials::remove_cg(unsigned idx, monomial& m) {
        monomial& sv = m_monomials[idx];
        unsigned next = sv.next();
        unsigned prev = sv.prev();
        
        lpvar u = m.var(), w;
        // equivalence class of u:
        if (m_cg_table.find(u, w) && w == u) {
            m_cg_table.erase(u);
            // insert other representative:
            if (prev != idx) {
                m_cg_table.insert(m_monomials[prev].var());
            }
        }
        if (prev != idx) {
            m_monomials[next].prev() = prev;
            m_monomials[prev].next() = next;
            sv.next() = idx;
            sv.prev() = idx;
        }
    }

    /**
       \brief insert canonized monomials using v into a congruence table.
       Prior to insertion, the monomials are canonized according to the current
       variable equivalences. The canonized monomials (monomial) are considered
       in the same equivalence class if they have the same set of representative
       variables. Their signs may differ.       
    */
    void emonomials::insert_cg(lpvar v) {
        cell* c = m_use_lists[v].m_head;
        if (c == nullptr) {
            return;
        }

        cell* first = c;
        inc_visited();
        do {
            unsigned idx = c->m_index;
            c = c->m_next;
            monomial & m = m_monomials[idx];
            if (!is_visited(m)) {
                set_visited(m);
                insert_cg(idx, m);
            }
        }
        while (c != first);
    }

    void emonomials::insert_cg(unsigned idx, monomial & m) {
        do_canonize(m);
        lpvar v = m.var(), w;
        if (m_cg_table.find(v, w)) {
            SASSERT(w != v);
            unsigned idxr = m_var2index[w];
            unsigned idxl = m_monomials[idxr].prev();
            m_monomials[idx].next()  = idxr;
            m_monomials[idx].prev()  = idxl;
            m_monomials[idxr].prev() = idx;
            m_monomials[idxl].next() = idx;
        }
        else {
            m_cg_table.insert(v);
            SASSERT(m_monomials[idx].next() == idx);
            SASSERT(m_monomials[idx].prev() == idx);
        }        
    }

    void emonomials::set_visited(monomial& m) const {
        m_monomials[m_var2index[m.var()]].visited() = m_visited;
    }

    bool emonomials::is_visited(monomial const& m) const {
        return m_visited == m_monomials[m_var2index[m.var()]].visited();
    }

    /**
       \brief insert a new monomial.

       Assume that the variables are canonical, that is, not equal in current
       context to another variable. The monomial is inserted into a congruence
       class of equal up-to var_eqs monomials.
     */
    void emonomials::add(lpvar v, unsigned sz, lpvar const* vs) {
        unsigned idx = m_monomials.size();
        m_monomials.push_back(monomial(v, sz, vs, idx));
        lpvar last_var = UINT_MAX;
        for (unsigned i = 0; i < sz; ++i) {
            lpvar w = vs[i];
            SASSERT(m_ve.is_root(w));
            if (w != last_var) {
                m_use_lists.reserve(w + 1);
                insert_cell(m_use_lists[w], idx);
                last_var = w; 
            }
        }
        SASSERT(m_ve.is_root(v));
        m_var2index.setx(v, idx, UINT_MAX);
        insert_cg(idx, m_monomials[idx]);
    }

    void emonomials::do_canonize(monomial & m) const {
        m.reset_rfields();
        for (lpvar v : m.vars()) {
            m.push_rvar(m_ve.find(v));
        }
        m.sort_rvars();
    }

    bool emonomials::canonize_divides(monomial& m, monomial & n) const {
        if (m.size() > n.size()) return false;
        unsigned ms = m.size(), ns = n.size();
        unsigned i = 0, j = 0;
        while (true) {
            if (i == ms) {
                return true;
            }
            else if (j == ns) {
                return false;
            }
            else if (m.rvars()[i] == n.rvars()[j]) {
                ++i; ++j;
            }
            else if (m.rvars()[i] < n.rvars()[j]) {
                return false;
            }
            else {
                ++j;
            }
        }
    }

// yes, assume that monomials are non-empty.
    emonomials::pf_iterator::pf_iterator(emonomials const& m, monomial & mon, bool at_end):
        m_em(m), m_mon(&mon), m_it(iterator(m, m.head(mon.vars()[0]), at_end)), m_end(iterator(m, m.head(mon.vars()[0]), true)) {
        fast_forward();
    }

    emonomials::pf_iterator::pf_iterator(emonomials const& m, lpvar v, bool at_end):
        m_em(m), m_mon(nullptr), m_it(iterator(m, m.head(v), at_end)), m_end(iterator(m, m.head(v), true)) {
        fast_forward();
    }

    void emonomials::pf_iterator::fast_forward() {
        for (; m_it != m_end; ++m_it) {
            if (m_mon && m_mon->var() != (*m_it).var() && m_em.canonize_divides(*m_mon, *m_it) && !m_em.is_visited(*m_it)) {
                m_em.set_visited(*m_it);
                break;
            }
            if (!m_mon && !m_em.is_visited(*m_it)) {
                m_em.set_visited(*m_it);
                break;
            }
        }
    }

    void emonomials::merge_eh(signed_var r2, signed_var r1, signed_var v2, signed_var v1) {
        // no-op
    }

    void emonomials::after_merge_eh(signed_var r2, signed_var r1, signed_var v2, signed_var v1) {
        if (!r2.sign() && m_ve.find(~r2) != m_ve.find(r1)) {
            m_use_lists.reserve(std::max(r2.var(), r1.var()) + 1);
            rehash_cg(r1.var()); 
            merge_cells(m_use_lists[r2.var()], m_use_lists[r1.var()]);
        }   
    }

    void emonomials::unmerge_eh(signed_var r2, signed_var r1) {
        if (!r2.sign() && m_ve.find(~r2) != m_ve.find(r1)) {
            unmerge_cells(m_use_lists[r2.var()], m_use_lists[r1.var()]);            
            rehash_cg(r1.var());
        }        
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
