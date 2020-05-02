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

  replaced rooted_mons.h and rooted_mon, rooted_mon_tabled

--*/

#include "math/lp/emonics.h"
#include "math/lp/nla_defs.h"
#include "math/lp/nla_core.h"

namespace nla {


void emonics::inc_visited() const {
    ++m_visited;
    if (m_visited == 0) {
        for (auto& svt : m_monics) {
            svt.set_visited(0);
        }
        ++m_visited;
    }
}

void emonics::push() {
    TRACE("nla_solver_mons", display(tout << "push\n"););
    SASSERT(invariant());
    m_u_f_stack.push_scope();
    m_lim.push_back(m_monics.size());
    m_region.push_scope();
    m_ve.push();
    SASSERT(monics_are_canonized());
    SASSERT(invariant());
}

void emonics::pop(unsigned n) {
    TRACE("nla_solver_mons", tout << "pop: " << n << "\n";);
    SASSERT(invariant());
    for (unsigned j = 0; j < n; ++j) {
        unsigned old_sz = m_lim[m_lim.size() - 1];
        for (unsigned i = m_monics.size(); i-- > old_sz; ) {
            m_ve.pop(1);
            monic & m = m_monics[i];
            TRACE("nla_solver_mons", display(tout << m << "\n"););
            remove_cg_mon(m);
            m_var2index[m.var()] = UINT_MAX;
            do_canonize(m);
            // variables in vs are in the same state as they were when add was called
            lpvar last_var = UINT_MAX;
            for (lpvar v : m.rvars()) {
                if (v != last_var) {
                    remove_cell(m_use_lists[v]);
                    last_var = v;
                }
            }
            m_ve.pop(1);
        }
        m_ve.pop(1);
        m_monics.shrink(old_sz);
        m_region.pop_scope(1);
        m_lim.pop_back();
        m_u_f_stack.pop_scope(1);
        SASSERT(invariant());
        SASSERT(monics_are_canonized());
    }
}

void emonics::remove_cell(head_tail& v) {
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

    TRACE("nla_solver_mons", 
          display(tout << "other: ", other_head) << "\n";
          display(tout << "root: ",  root_head) << "\n"; );

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
    TRACE("nla_solver_mons", 
          display(tout << "other: ", other_head) << "\n";
          display(tout << "root: ",  root_head) << "\n"; );          
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
    if (m_cg_table.contains(UINT_MAX) && !m_cg_table[UINT_MAX].empty()) {
        lpvar w = m_cg_table[UINT_MAX][0];
        result = &m_monics[m_var2index[w]];
    }
    return result;
}

void emonics::remove_cg(lpvar v) {
    TRACE("nla_solver_mons", tout << "remove: " << v << "\n";);
//    TRACE("nla_solver_mons", display(tout););
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
    lpvar u = m.var();
    // equivalence class of u:
    auto& v = m_cg_table[u];
    SASSERT(v.contains(u));
    if (v.size() == 1) {
        m_cg_table.remove(u);
    }
    else if (v[0] == u) {
        v.erase(u);
        auto v0 = v[0];
        unsigned_vector vv(v);
        m_cg_table.remove(u);
        m_cg_table.insert(v0, vv);
    }
    else {
        v.erase(u);
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
        TRACE("nla_solver_mons", tout << "inserting v" << v << " for " << idx << "\n";);
        monic & m = m_monics[idx];
        if (!is_visited(m)) {
            set_visited(m);
            insert_cg_mon(m);
        }
    }
    while (c != first);
    TRACE("nla_solver_mons", tout << "insert: " << v << "\n";);    
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
        // bail out of invariant check
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
               }
               display(tout);
               );
        SASSERT(c == it->second);
    }
    return true;
}


void emonics::insert_cg_mon(monic & m) {
    do_canonize(m);
    lpvar v = m.var(), w;
    TRACE("nla_solver_mons", tout << m << "\n";); //  hash: " << m_cg_hash(v) << "\n";);
    auto& vec = m_cg_table.insert_if_not_there(v, unsigned_vector());
    if (vec.empty()) {
        vec.push_back(v);
    }
    else if (!vec.contains(v)) {
        w = vec[0];
        vec.push_back(v);
        unsigned v_idx = m_var2index[v];
        unsigned w_idx = m_var2index[w];
        unsigned max_i = std::max(v_idx, w_idx);
        while (m_u_f.get_num_vars() <= max_i)
            m_u_f.mk_var();
        TRACE("nla_solver_mons", tout << "merge " << v << " idx " << v_idx << ", and " << w << " idx " << w_idx << "\n";);
        m_u_f.merge(v_idx, w_idx);
    }
    else {
        TRACE("nla_solver_mons", tout << "found "  << v << "\n";);
    }
}

void emonics::set_visited(monic& m) const {
    m_monics[m_var2index[m.var()]].set_visited(m_visited);
}

bool emonics::is_visited(monic const& m) const {
    return m_visited == m_monics[m_var2index[m.var()]].visited();
}

/**
   \brief insert a new monic.

   Assume that the main variable is canonical and unique.
   Variables in the arguments could be non-caninical.
   They are canonized before the new monic is created.
   The monic is inserted into a congruence class of equal up-to var_eqs monics.
*/
void emonics::add(lpvar v, unsigned sz, lpvar const* vs) {
    TRACE("nla_solver_mons", tout << "v = " << v << "\n";);
    SASSERT(m_ve.is_root(v));
    SASSERT(!is_monic_var(v));
    SASSERT(invariant());
    m_ve.push();
    unsigned idx = m_monics.size();
    m_monics.push_back(monic(v, sz, vs, idx));
    do_canonize(m_monics.back());

    // variables in m_vs are canonical and sorted, 
    // so use last_var to skip duplicates, 
    // while updating use-lists
    lpvar last_var = UINT_MAX;
    for (lpvar w : m_monics.back().rvars()) {
        if (w != last_var) {
            m_use_lists.reserve(w + 1);
            insert_cell(m_use_lists[w], idx);
            last_var = w; 
        }
    }
    m_var2index.setx(v, idx, UINT_MAX);
    insert_cg_mon(m_monics[idx]);
    SASSERT(invariant());
    m_ve.push();
}

void emonics::do_canonize(monic & m) const {
    TRACE("nla_solver_mons", tout << m << "\n";);
    m.reset_rfields();
    for (lpvar v : m.vars()) {
        m.push_rvar(m_ve.find(v));
    }
    m.sort_rvars();
    TRACE("nla_solver_mons", tout << m << "\n";);
}

bool emonics::is_canonized(const monic & m) const {
    monic mm(m);
    do_canonize(mm);
    return mm.rvars() == m.rvars();
}

void emonics::ensure_canonized() {
    for (auto & m : m_monics) {
        do_canonize(m);
    }
}

bool emonics::monics_are_canonized() const {
    for (auto & m: m_monics) {
        if (!is_canonized(m)) {
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
    m_em(m), m_mon(&mon), 
    m_it(iterator(m, m.head(mon.vars()[0]), at_end)), 
    m_end(iterator(m, m.head(mon.vars()[0]), true)) {
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
    TRACE("nla_solver_mons", tout << v2 << " <- " << v1 << " : " << r2 << " <- " << r1 << "\n";);
    if (r1.var() == r2.var() || m_ve.find(~r1) == m_ve.find(~r2)) { // the other sign has also been merged
        TRACE("nla_solver_mons", 
              display_uf(tout << r2 << " <- " << r1 << "\n");
              tout << "rehashing " << r1.var() << "\n";);
        m_use_lists.reserve(std::max(r2.var(), r1.var()) + 1);
        rehash_cg(r1.var()); 
        merge_cells(m_use_lists[r2.var()], m_use_lists[r1.var()]);
    }   
}

void emonics::unmerge_eh(signed_var r2, signed_var r1) {
    if (r1.var() == r2.var() || m_ve.find(~r1) != m_ve.find(~r2)) { // the other sign has also been unmerged
        TRACE("nla_solver_mons", tout << r2 << " -> " << r1 << "\n";);
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
    display_use(out);
    //display_uf(out);
    return out;
}

std::ostream& emonics::display(std::ostream& out) const {
    out << "monics\n";
    unsigned idx = 0;
    for (auto const& m : m_monics) {
        out << "m" << (idx++) << ": " << m << "\n";
    }    
    display_use(out);
    display_uf(out);
    out << "table:\n";
    for (auto const& k : m_cg_table) {
        out << k.m_key << ": " << k.m_value << "\n";
    }
    return out;
}
 
std::ostream& emonics::display_use(std::ostream& out) const {
    out << "use lists\n";
    unsigned v = 0;
    for (auto const& ht : m_use_lists) {
        cell* c = ht.m_head;
        if (c) {
            out << v << ": ";
            do {
                out << "m" << c->m_index << " ";
                c = c->m_next;
            }
            while (c != ht.m_head);
            out << "\n";
        }
        ++v;
     }
    return out;
}

std::ostream& emonics::display_uf(std::ostream& out) const {
    m_u_f.display(out << "uf\n");
    m_ve.display(out << "ve\n");
    return out;
}

std::ostream& emonics::display(std::ostream& out, cell* c) const {
    cell* c0 = c;
    if (c) {
        do {
            out << c->m_index << " ";
            c = c->m_next;
        }
        while (c != c0);
    }
    return out;
}


bool emonics::invariant() const {
    TRACE("nla_solver_mons", display(tout););
    // the varible index contains exactly the active monomials
    unsigned mons = 0;
    for (lpvar v = 0; v < m_var2index.size(); v++) {
        if (is_monic_var(v)) {
            mons++;
        }
    }
    if (m_monics.size() != mons) {
        TRACE("nla_solver_mons", tout << "missmatch of monic vars\n";);
        return false;
    }

    // check that every monomial in the 
    // use list of v contains v.
    unsigned v = 0;
    for (auto const& ht : m_use_lists) {
        cell* c = ht.m_head;
        if (c) {
            auto v1 = m_ve.find(v);
            do {
                auto const& m = m_monics[c->m_index];
                bool found = false;
                for (lp::var_index w : m.rvars()) {
                    auto w1 = m_ve.find(w);
                    found |= v1.var() == w1.var();
                }
                CTRACE("nla_solver_mons", !found, tout << "not found v" << v << ": " << m << "\n";);
                SASSERT(found);
                c = c->m_next;
            }
            while (c != ht.m_head);
        }
        v++;
    }

    // all monomials are in congruence table.
    // the variables of each monomial contain the monomial in their use-list
    std::function<bool(lpvar, unsigned)> find_index = [&,this](lpvar v, unsigned idx) {
        cell* c = m_use_lists[v].m_head;
        cell* c0 = c;
        if (!c)
            return false;
        bool found = false;
        do {
            found |= c->m_index == idx;
            c = c->m_next;
        }
        while (c != c0 && !found);
        CTRACE("nla_solver_mons", !found, tout << "m" << idx << " not found in use list for v" << v << "\n";);
        return found;
    };
    unsigned idx = 0;
    for (auto const& m : m_monics) {
        CTRACE("nla_solver_mons", !m_cg_table.contains(m.var()), tout << "removed " << m << "\n"; );
        SASSERT(m_cg_table.contains(m.var()));
        SASSERT(m_cg_table[m.var()].contains(m.var()));
        // same with rooted variables
        for (auto v : m.rvars()) {
            if (!find_index(v, idx)) {
                TRACE("nla_solver_mons", tout << "rooted var not found in monic use list" << v << "\n";);
                return false;
            }
        }
        idx++;
    }
    
    // the table of monic representatives is such that the
    // first entry in the vector is the equivalence class
    // representative.
    for (auto const& k : m_cg_table) {
        auto const& v = k.m_value;
        if (!v.empty() && v[0] != k.m_key) {
            TRACE("nla_solver_mons", tout << "bad table entry: " << k.m_key << ": " << k.m_value << "\n";);
            return false;
        }
    }

    return true;
}

}
