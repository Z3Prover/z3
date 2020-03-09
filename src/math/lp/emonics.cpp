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

#include "math/lp/emonics.h"
#include "math/lp/nla_defs.h"
#include "math/lp/nla_core.h"

namespace nla {


void emonics::inc_visited() const {
    ++m_visited;
    if (m_visited == 0) {
        for (auto& svt : m_monics) {
            svt.visited() = 0;
        }
        ++m_visited;
    }
}

void emonics::push() {
    m_u_f_stack.push_scope();
    m_lim.push_back(m_monics.size());
    m_region.push_scope();
    m_ve.push();
    SASSERT(monics_are_canonized());
}

void emonics::pop(unsigned n) {
    m_ve.pop(n);
    unsigned old_sz = m_lim[m_lim.size() - n];
    for (unsigned i = m_monics.size(); i-- > old_sz; ) {
        monic & m = m_monics[i];
        remove_cg_mon(m);
        m_var2index[m.var()] = UINT_MAX;
        lpvar last_var = UINT_MAX;
        for (lpvar v : m.vars()) {
            if (v != last_var) {
                remove_cell(m_use_lists[v], i);
                last_var = v;
            }
        }
    }
    m_monics.shrink(old_sz);
    m_monics.shrink(old_sz);
    m_region.pop_scope(n);
    m_lim.shrink(m_lim.size() - n);
    SASSERT(monics_are_canonized());
    m_u_f_stack.pop_scope(n);
}

void emonics::remove_cell(head_tail& v, unsigned mIndex) {
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

void emonics::insert_cell(head_tail& v, unsigned mIndex) {
    cell*& cur_head = v.m_head;
    cell*& cur_tail = v.m_tail;
    cell* new_head = new (m_region) cell(mIndex, cur_head);
    cur_head = new_head;
    if (!cur_tail) cur_tail = new_head;
    cur_tail->m_next = new_head;
}

void emonics::merge_cells(head_tail& root, head_tail& other) {
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

void emonics::unmerge_cells(head_tail& root, head_tail& other) {
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

emonics::cell* emonics::head(lpvar v) const {
    v = m_ve.find(v).var();
    m_use_lists.reserve(v + 1);
    return m_use_lists[v].m_head;
}

monic const* emonics::find_canonical(svector<lpvar> const& vars) const {
    SASSERT(m_ve.is_root(vars));
    m_find_key = vars;
    std::sort(m_find_key.begin(), m_find_key.end());
    monic const* result = nullptr;
    lpvar w;
    if (m_cg_table.find(UINT_MAX, w)) {
        result = &m_monics[m_var2index[w]];
    }
    return result;
}


void emonics::remove_cg(lpvar v) {
    cell* c = m_use_lists[v].m_head;
    if (c == nullptr) {
        return;
    }
    cell* first = c;
    inc_visited();
    do {
        unsigned idx = c->m_index;
        c = c->m_next;
        monic & m = m_monics[idx];
        if (!is_visited(m)) {
            set_visited(m);
            remove_cg_mon(m);
        }
    }
    while (c != first);
}

void emonics::remove_cg_mon(const monic& m) {
    lpvar u = m.var(), w;
    // equivalence class of u:
    if (m_cg_table.find(u, w)) {
        TRACE("nla_solver_mons", tout << "erase << " << m << "\n";);
        m_cg_table.erase(u);
    }
}

/**
   \brief insert canonized monics using v into a congruence table.
   Prior to insertion, the monics are canonized according to the current
   variable equivalences. The canonized monics (monic) are considered
   in the same equivalence class if they have the same set of representative
   variables. Their signs may differ.       
*/
void emonics::insert_cg(lpvar v) {
    cell* c = m_use_lists[v].m_head;

    if (c == nullptr) {
        return;
    }

    cell* first = c;
    inc_visited();
    do {
        unsigned idx = c->m_index;
        c = c->m_next;
        monic & m = m_monics[idx];
        if (!is_visited(m)) {
            set_visited(m);
            insert_cg_mon(m);
        }
    }
    while (c != first);
}

bool emonics::elists_are_consistent(std::unordered_map<unsigned_vector, std::unordered_set<lpvar>, hash_svector>& lists) const {    
    for (auto const & m : m_monics) {
        auto it = lists.find(m.rvars());
        if (it == lists.end()) {
            std::unordered_set<lpvar> v;
            v.insert(m.var());
            lists[m.rvars()] = v;            
        } else {
            it->second.insert(m.var());
        }
    }
    for (auto const & m : m_monics) {
        SASSERT(is_canonized(m));
        if (!is_canonical_monic(m.var()))
            continue;
        std::unordered_set<lpvar> c;
        for (const monic& e : enum_sign_equiv_monics(m))
            c.insert(e.var());
        auto it = lists.find(m.rvars());
        (void)it;
        CTRACE("nla_solver_mons",  it->second != c,
               tout << "m = " << m << "\n";
               tout << "c = " ; print_vector(c, tout); tout << "\n";
               if (it == lists.end()) {
                   tout << "m.rvars are not found\n";
               }
               else {
                   tout << "it->second = "; print_vector(it->second, tout); tout << "\n";
                   for (unsigned j : it->second) {
                       tout << (*this)[j] << "\n";
                   }
               });
        SASSERT(c == it->second);
    }
    return true;
}


void emonics::insert_cg_mon(monic & m) {
    do_canonize(m);
    lpvar v = m.var(), w;
    if (m_cg_table.find(v, w)) {
        if (v == w) {
            TRACE("nla_solver_mons", tout << "found "  << v << "\n";);
            return;
        }
        unsigned v_idx = m_var2index[v];
        unsigned w_idx = m_var2index[w];
        unsigned max_i = std::max(v_idx, w_idx);
        while (m_u_f.get_num_vars() <= max_i)
            m_u_f.mk_var();
        TRACE("nla_solver_mons", tout << "merge " << v << " idx " << v_idx << ", and " << w << " idx " << w_idx << "\n";);
        m_u_f.merge(v_idx, w_idx);
    }
    else {
        TRACE("nla_solver_mons", tout << "insert " << m << "\n";);
        m_cg_table.insert(v);
    }        
}

void emonics::set_visited(monic& m) const {
    m_monics[m_var2index[m.var()]].visited() = m_visited;
}

bool emonics::is_visited(monic const& m) const {
    return m_visited == m_monics[m_var2index[m.var()]].visited();
}

/**
   \brief insert a new monic.

   Assume that the variables are canonical, that is, not equal in current
   context to another variable. The monic is inserted into a congruence
   class of equal up-to var_eqs monics.
*/
void emonics::add(lpvar v, unsigned sz, lpvar const* vs) {
    TRACE("nla_solver_mons", tout << "v = " << v << "\n";);
    unsigned idx = m_monics.size();
    m_monics.push_back(monic(v, sz, vs, idx));
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
    insert_cg_mon(m_monics[idx]);
}

void emonics::do_canonize(monic & m) const {
    m.reset_rfields();
    for (lpvar v : m.vars()) {
        m.push_rvar(m_ve.find(v));
    }
    m.sort_rvars();
}

bool emonics::is_canonized(const monic & m) const {
    monic mm(m);
    do_canonize(mm);
    return mm.rvars() == m.rvars();
}

bool emonics:: monics_are_canonized() const {
    for (auto & m: m_monics) {
        if (! is_canonized(m)) {
            return false;
        }
    }
    return true;
}


bool emonics::canonize_divides(monic& m, monic & n) const {
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

// yes, assume that monics are non-empty.
emonics::pf_iterator::pf_iterator(emonics const& m, monic & mon, bool at_end):
    m_em(m), m_mon(&mon), m_it(iterator(m, m.head(mon.vars()[0]), at_end)), m_end(iterator(m, m.head(mon.vars()[0]), true)) {
    fast_forward();
}

emonics::pf_iterator::pf_iterator(emonics const& m, lpvar v, bool at_end):
    m_em(m), m_mon(nullptr), m_it(iterator(m, m.head(v), at_end)), m_end(iterator(m, m.head(v), true)) {
    fast_forward();
}

void emonics::pf_iterator::fast_forward() {
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

void emonics::merge_eh(signed_var r2, signed_var r1, signed_var v2, signed_var v1) {
    // no-op
}

void emonics::after_merge_eh(signed_var r2, signed_var r1, signed_var v2, signed_var v1) {
    TRACE("nla_solver_mons", tout << r2 << " <- " << r1 << "\n";);
    if (m_ve.find(~r1) == m_ve.find(~r2)) { // the other sign has also been merged
        m_use_lists.reserve(std::max(r2.var(), r1.var()) + 1);
        TRACE("nla_solver_mons", tout << "rehasing " << r1.var() << "\n";);
        merge_cells(m_use_lists[r2.var()], m_use_lists[r1.var()]);
        rehash_cg(r1.var()); 
    }   
}

void emonics::unmerge_eh(signed_var r2, signed_var r1) {
    TRACE("nla_solver_mons", tout << r2 << " -> " << r1 << "\n";);
    if (m_ve.find(~r1) != m_ve.find(~r2)) { // the other sign has also been unmerged
        unmerge_cells(m_use_lists[r2.var()], m_use_lists[r1.var()]);            
        rehash_cg(r1.var());
    }        
}

std::ostream& emonics::display(const core& cr, std::ostream& out) const {
    out << "monics\n";
    unsigned idx = 0;
    for (auto const& m : m_monics) {
        out << "m" << (idx++) << ": " << pp_mon_with_vars(cr, m) << "\n";
    }    
    return display_use(out);
}

std::ostream& emonics::display(std::ostream& out) const {
    out << "monics\n";
    unsigned idx = 0;
    for (auto const& m : m_monics) {
        out << "m" << (idx++) << ": " << m << "\n";
    }    
    return display_use(out);
}
 
 std::ostream& emonics::display_use(std::ostream& out) const {
     out << "use lists\n";
     unsigned idx = 0;
     for (auto const& ht : m_use_lists) {
         cell* c = ht.m_head;
         if (c) {
             out << idx << ": ";
             do {
                 out << "m" << c->m_index << " ";
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
