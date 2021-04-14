/*++
  Copyright (c) 2019 Microsoft Corporation

  Module Name:

     emonomials.h

  Abstract:

     table that associate monomials to congruence class representatives modulo a union find structure.

  Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)

  Revision History:

    to replace rooted_mons.h and rooted_mon, rooted_mon_tabled

  --*/

#pragma once
#include "math/lp/lp_utils.h"
#include "math/lp/var_eqs.h"
#include "math/lp/monic.h"
#include "util/region.h"
#include "util/map.h"

namespace nla {

struct hash_svector {
    size_t operator()(const unsigned_vector & v) const {
        return svector_hash<unsigned_hash>()(v);
    }
};

class core;

class emonics {
    /**
       \brief singly-lined cyclic list of monic indices where variable occurs.
       Each variable points to the head and tail of the cyclic list.
       Initially, head and tail are nullptr.
       New elements are inserted in the beginning of the list.
       Two lists are merged when equivalence class representatives are merged, 
       and the merge is undone when the representative variables are unmerged.
    */
    struct cell {
        cell(unsigned mIndex, cell* c): m_next(c), m_index(mIndex) {}
        cell*        m_next;
        unsigned     m_index;
    };
    struct head_tail {
        head_tail(): m_head(nullptr), m_tail(nullptr) {}
        cell* m_head;
        cell* m_tail;
    };
    struct hash_canonical {
        emonics& em;
        hash_canonical(emonics& em): em(em) {}
            
        unsigned operator()(lpvar v) const {
            auto const& vec = v != UINT_MAX? em.m_monics[em.m_var2index[v]].rvars() : em.m_find_key;
            return string_hash(reinterpret_cast<char const*>(vec.data()), sizeof(lpvar)*vec.size(), 10);
        }
    };
        


    /**
       \brief private fields used by emonics for maintaining state of canonized monics.
    */

    struct eq_canonical {
        emonics& em;
        eq_canonical(emonics& em): em(em) {}
        bool operator()(lpvar u, lpvar v) const {
            auto const& uvec = u != UINT_MAX? em.m_monics[em.m_var2index[u]].rvars(): em.m_find_key;
            auto const& vvec = v != UINT_MAX? em.m_monics[em.m_var2index[v]].rvars(): em.m_find_key;
            return uvec == vvec;
        }
    };
    
    union_find<emonics>          m_u_f;
    trail_stack                  m_u_f_stack;
    mutable svector<lpvar>       m_find_key; // the key used when looking for a monic with the specific variables
    var_eqs<emonics>&            m_ve;
    mutable vector<monic>        m_monics;     // set of monics
    mutable unsigned_vector      m_var2index;     // var_mIndex -> mIndex
    unsigned_vector              m_lim;           // backtracking point
    mutable unsigned             m_visited;       // timestamp of visited monics during pf_iterator
    region                       m_region;        // region for allocating linked lists
    mutable svector<head_tail>   m_use_lists;     // use list of monics where variables occur.
    hash_canonical               m_cg_hash;
    eq_canonical                 m_cg_eq;
    map<lpvar, unsigned_vector, hash_canonical, eq_canonical> m_cg_table; // congruence (canonical) table.


    void inc_visited() const;

    void remove_cell(head_tail& v);
    void insert_cell(head_tail& v, unsigned mIndex);
    void merge_cells(head_tail& root, head_tail& other);
    void unmerge_cells(head_tail& root, head_tail& other);

    void remove_cg(lpvar v);
    void insert_cg(lpvar v);
    void insert_cg_mon(monic & m);
    void remove_cg_mon(const monic & m);
    void rehash_cg(lpvar v) { remove_cg(v); insert_cg(v); }
    void do_canonize(monic& m) const; 
    cell* head(lpvar v) const;
    void set_visited(monic& m) const;
    bool is_visited(monic const& m) const;
    std::ostream& display_use(std::ostream& out) const; 
    std::ostream& display_uf(std::ostream& out) const; 
    std::ostream& display(std::ostream& out, cell* c) const;
public:
    unsigned number_of_monics() const { return m_monics.size(); }
    /**
       \brief emonics builds on top of var_eqs.
       push and pop on emonics calls push/pop on var_eqs, so no 
       other calls to push/pop to the var_eqs should take place. 
    */
    emonics(var_eqs<emonics>& ve):
        m_u_f(*this),
        m_u_f_stack(),
        m_ve(ve), 
        m_visited(0), 
        m_cg_hash(*this),
        m_cg_eq(*this),
        m_cg_table(m_cg_hash, m_cg_eq) { 
        m_ve.set_merge_handler(this); 
    }

    void unmerge_eh(unsigned i, unsigned j) {
        TRACE("nla_solver", tout << "unmerged " << i << " and " << j << "\n";);
    }
    
    void merge_eh(unsigned r2, unsigned r1, unsigned v2, unsigned v1) {}
    void after_merge_eh(unsigned r2, unsigned r1, unsigned v2, unsigned v1) {}

    // this method is required by union_find
    trail_stack & get_trail_stack() { return m_u_f_stack; }

    /**
       \brief push/pop scopes. 
       The life-time of a merge is local within a scope.
    */
    void push();

    void pop(unsigned n);

    /**
       \brief create a monic from an equality v := vs
    */
    void add(lpvar v, unsigned sz, lpvar const* vs);
    void add(lpvar v, svector<lpvar> const& vs) { add(v, vs.size(), vs.data()); }
    void add(lpvar v, lpvar x, lpvar y) { lpvar vs[2] = { x, y }; add(v, 2, vs); }
    void add(lpvar v, lpvar x, lpvar y, lpvar z) { lpvar vs[3] = { x, y, z }; add(v, 3, vs); }

    /**
       \brief retrieve monic corresponding to variable v from definition v := vs
    */
    monic const& operator[](lpvar v) const { return m_monics[m_var2index[v]]; }
    monic & operator[](lpvar v) { return m_monics[m_var2index[v]]; }
    bool is_canonized(const monic&) const;    
    bool monics_are_canonized() const;
    void ensure_canonized();
 
    /**
       \brief obtain the representative canonized monic 
    */

    monic const& rep(monic const& sv) const {
        unsigned j = m_cg_table[sv.var()][0];
        return m_monics[m_var2index[j]];
    }

    /**
       \brief determine if m1 divides m2 over the canonization obtained from merged variables.
    */
    bool canonize_divides(monic & m1, monic& m2) const;

    /**
       \brief iterator over monics that are declared.
    */
    vector<monic>::const_iterator begin() const { return m_monics.begin(); }
    vector<monic>::const_iterator end() const { return m_monics.end(); }

    /**
       \brief iterators over monics where a variable is used
    */
    class iterator {
        emonics const& m;
        cell*       m_cell;
        bool        m_touched;            
    public:
        iterator(emonics const& m, cell* c, bool at_end): m(m), m_cell(c), m_touched(at_end || c == nullptr) {}
        monic & operator*() { return m.m_monics[m_cell->m_index]; }
        iterator& operator++() { m_touched = true; m_cell = m_cell->m_next; return *this; }
        iterator operator++(int) { iterator tmp = *this; ++*this; return tmp; }
        bool operator==(iterator const& other) const { return m_cell == other.m_cell && m_touched == other.m_touched; }
        bool operator!=(iterator const& other) const { return m_cell != other.m_cell || m_touched != other.m_touched; }
    };
        
    class use_list {
        emonics const& m;
        lpvar     m_var;
        cell*     head() { return m.head(m_var); } 
    public:
        use_list(emonics const& m, lpvar v): m(m), m_var(v) {}
        iterator begin() { return iterator(m, head(), false); }
        iterator end() { return iterator(m, head(), true); }
    };

    use_list get_use_list(lpvar v) const { return use_list(*this, v); }

    /**
       \brief retrieve monics m' where m is a proper factor of modulo current equalities.
    */
    class pf_iterator {
        emonics const& m_em;
        monic *           m_mon;
        iterator          m_it;  // iterator over the first variable occurs list, ++ filters out elements that do not have m as a factor
        iterator          m_end;

        void fast_forward();
    public:
        pf_iterator(emonics const& m, monic& mon, bool at_end);
        pf_iterator(emonics const& m, lpvar v, bool at_end);
        monic & operator*() {
            return *m_it;
        }
        pf_iterator& operator++() { ++m_it; fast_forward(); return *this; }
        pf_iterator operator++(int) { pf_iterator tmp = *this; ++*this; return tmp; }
        bool operator==(pf_iterator const& other) const { return m_it == other.m_it; }
        bool operator!=(pf_iterator const& other) const { return m_it != other.m_it; }
    };

    class products_of {
        emonics const& m;
        monic *        mon;
        lpvar          m_var;
    public:
        products_of(emonics const& m, monic & mon): m(m), mon(&mon), m_var(UINT_MAX) {}
        products_of(emonics const& m, lpvar v): m(m), mon(nullptr), m_var(v) {}
        pf_iterator begin() { if (mon) return pf_iterator(m, *mon, false); return pf_iterator(m, m_var, false); }
        pf_iterator end() { if (mon) return pf_iterator(m, *mon, true); return pf_iterator(m, m_var, true); }
    };

    products_of get_products_of(monic& m) const { inc_visited(); return products_of(*this, m); }
    products_of get_products_of(lpvar v) const { inc_visited(); return products_of(*this, v); }
       
    monic const* find_canonical(svector<lpvar> const& vars) const;
    bool is_canonical_monic(lpvar j) const {
        SASSERT(is_monic_var(j));
        unsigned idx = m_var2index[j];
        if (idx >= m_u_f.get_num_vars())
            return true;
        return m_u_f.find(idx) == idx;
    }
    /**
       \brief iterator over sign equivalent monics.
       These are monics that are equivalent modulo m_var_eqs amd modulo signs.
    */
    class sign_equiv_monics_it {
        emonics const& m;
        unsigned          m_index;
        bool              m_touched;
    public:
        sign_equiv_monics_it(emonics const& m, unsigned idx, bool at_end): 
            m(m), m_index(idx), m_touched(at_end) {}

        monic const& operator*() { return m.m_monics[m_index]; }

        sign_equiv_monics_it& operator++() { 
            m_touched = true;
            if (m_index < m.m_u_f.get_num_vars())
                m_index = m.m_u_f.next(m_index);
            return *this; 
        }

        sign_equiv_monics_it operator++(int) { 
            sign_equiv_monics_it tmp = *this; 
            ++*this; 
            return tmp; 
        }

        bool operator==(sign_equiv_monics_it const& other) const { 
            return m_index == other.m_index && m_touched == other.m_touched; 
        }

        bool operator!=(sign_equiv_monics_it const& other) const { 
            return m_index != other.m_index || m_touched != other.m_touched; 
        }
    };

    class sign_equiv_monics {
        const emonics&     em;
        monic const& m;
        unsigned index() const { return em.m_var2index[m.var()]; }
    public:
        sign_equiv_monics(const emonics & em, monic const& m): em(em), m(m) {}
        sign_equiv_monics_it begin() { return sign_equiv_monics_it(em, index(), false); }
        sign_equiv_monics_it end() { return sign_equiv_monics_it(em, index(), true); }
    };

    sign_equiv_monics enum_sign_equiv_monics(monic const& m) const { return sign_equiv_monics(*this, m); }
    sign_equiv_monics enum_sign_equiv_monics(lpvar v) { return enum_sign_equiv_monics((*this)[v]); }
    /**
       \brief display state of emonics
    */
    std::ostream& display(const core&, std::ostream& out) const;
    std::ostream& display(std::ostream& out) const;

    /**
       \brief
       these are merge event handlers to interect the union-find handlers.
       r2 becomes the new root. r2 is the root of v2, r1 is the old root of v1
    */
    void merge_eh(signed_var r2, signed_var r1, signed_var v2, signed_var v1);

    void after_merge_eh(signed_var r2, signed_var r1, signed_var v2, signed_var v1);

    void unmerge_eh(signed_var r2, signed_var r1);        

    bool is_monic_var(lpvar v) const { return m_var2index.get(v, UINT_MAX) != UINT_MAX; }

    bool is_used_in_monic(lpvar v) const { return v < m_use_lists.size() && m_use_lists[v].m_head != nullptr; }

    bool elists_are_consistent(std::unordered_map<unsigned_vector, std::unordered_set<lpvar>, hash_svector> &lists) const;

    bool invariant() const;
    
}; // end of emonics

struct pp_emons {
    const core&       m_c;
    const emonics& m_em;
    pp_emons(const core& c, const emonics& e): m_c(c), m_em(e) {}
    inline std::ostream& display(std::ostream& out) const {
        return m_em.display(m_c, out);
    }
};

inline std::ostream& operator<<(std::ostream& out, pp_emons const& p) { return p.display(out); }

}
