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
#include "util/lp/lp_utils.h"
#include "util/lp/var_eqs.h"
#include "util/lp/monomial.h"
#include "util/region.h"

namespace nla {

class core;

class emonomials {
    /**
       \brief singly-lined cyclic list of monomial indices where variable occurs.
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
        emonomials& em;
        hash_canonical(emonomials& em): em(em) {}
            
        unsigned operator()(lpvar v) const {
            auto const& vec = v != UINT_MAX? em.m_monomials[em.m_var2index[v]].rvars() : em.m_find_key;
            return string_hash(reinterpret_cast<char const*>(vec.c_ptr()), sizeof(lpvar)*vec.size(), 10);
        }
    };
        


    /**
       \brief private fields used by emonomials for maintaining state of canonized monomials.
    */

    struct eq_canonical {
        emonomials& em;
        eq_canonical(emonomials& em): em(em) {}
        bool operator()(lpvar u, lpvar v) const {
            auto const& uvec = u != UINT_MAX? em.m_monomials[em.m_var2index[u]].rvars(): em.m_find_key;
            auto const& vvec = v != UINT_MAX? em.m_monomials[em.m_var2index[v]].rvars(): em.m_find_key;
            return uvec == vvec;
        }
    };

    mutable svector<lpvar>            m_find_key; // the key used when looking for a monomial with the specific variables
    var_eqs<emonomials>&                        m_ve;
    mutable vector<monomial>        m_monomials;     // set of monomials
    mutable unsigned_vector         m_var2index;     // var_mIndex -> mIndex
    unsigned_vector                 m_lim;           // backtracking point
    mutable unsigned                m_visited;       // timestamp of visited monomials during pf_iterator
    region                          m_region;        // region for allocating linked lists
    mutable svector<head_tail>      m_use_lists;     // use list of monomials where variables occur.
    hash_canonical                  m_cg_hash;
    eq_canonical                    m_cg_eq;
    hashtable<lpvar, hash_canonical, eq_canonical> m_cg_table; // congruence (canonical) table.

    void inc_visited() const;

    void remove_cell(head_tail& v, unsigned mIndex);
    void insert_cell(head_tail& v, unsigned mIndex);
    void merge_cells(head_tail& root, head_tail& other);
    void unmerge_cells(head_tail& root, head_tail& other);

    void remove_cg(lpvar v);
    void insert_cg(lpvar v);
    void insert_cg(unsigned idx, monomial & m);
    void remove_cg(unsigned idx, monomial & m);
    void rehash_cg(lpvar v) { remove_cg(v); insert_cg(v); }

    void do_canonize(monomial& m) const; 
    cell* head(lpvar v) const;
    void set_visited(monomial& m) const;
    bool is_visited(monomial const& m) const;
    std::ostream& display_use(std::ostream& out) const; 
public:
    /**
       \brief emonomials builds on top of var_eqs.
       push and pop on emonomials calls push/pop on var_eqs, so no 
       other calls to push/pop to the var_eqs should take place. 
    */
    emonomials(var_eqs<emonomials>& ve): 
        m_ve(ve), 
        m_visited(0), 
        m_cg_hash(*this),
        m_cg_eq(*this),
        m_cg_table(DEFAULT_HASHTABLE_INITIAL_CAPACITY, m_cg_hash, m_cg_eq) { 
        m_ve.set_merge_handler(this); 
    }

    /**
       \brief push/pop scopes. 
       The life-time of a merge is local within a scope.
    */
    void push();

    void pop(unsigned n);

    /**
       \brief create a monomial from an equality v := vs
    */
    void add(lpvar v, unsigned sz, lpvar const* vs);
    void add(lpvar v, svector<lpvar> const& vs) { add(v, vs.size(), vs.c_ptr()); }
    void add(lpvar v, lpvar x, lpvar y) { lpvar vs[2] = { x, y }; add(v, 2, vs); }
    void add(lpvar v, lpvar x, lpvar y, lpvar z) { lpvar vs[3] = { x, y, z }; add(v, 3, vs); }

    /**
       \brief retrieve monomial corresponding to variable v from definition v := vs
    */
    monomial const& operator[](lpvar v) const { return m_monomials[m_var2index[v]]; }
    monomial & operator[](lpvar v) { return m_monomials[m_var2index[v]]; }
    bool is_canonized(const monomial&) const;    
    bool monomials_are_canonized() const;
    
    /**
       \brief obtain the representative canonized monomial 
    */

    monomial const& rep(monomial const& sv) const {
        unsigned j = -1;
        m_cg_table.find(sv.var(), j);
        return m_monomials[m_var2index[j]];
    }

    /**
       \brief determine if m1 divides m2 over the canonization obtained from merged variables.
    */
    bool canonize_divides(monomial & m1, monomial& m2) const;

    /**
       \brief iterator over monomials that are declared.
    */
    vector<monomial>::const_iterator begin() const { return m_monomials.begin(); }
    vector<monomial>::const_iterator end() const { return m_monomials.end(); }

    /**
       \brief iterators over monomials where a variable is used
    */
    class iterator {
        emonomials const& m;
        cell*       m_cell;
        bool        m_touched;            
    public:
        iterator(emonomials const& m, cell* c, bool at_end): m(m), m_cell(c), m_touched(at_end || c == nullptr) {}
        monomial & operator*() { return m.m_monomials[m_cell->m_index]; }
        iterator& operator++() { m_touched = true; m_cell = m_cell->m_next; return *this; }
        iterator operator++(int) { iterator tmp = *this; ++*this; return tmp; }
        bool operator==(iterator const& other) const { return m_cell == other.m_cell && m_touched == other.m_touched; }
        bool operator!=(iterator const& other) const { return m_cell != other.m_cell || m_touched != other.m_touched; }
    };
        
    class use_list {
        emonomials const& m;
        lpvar     m_var;
        cell*     head() { return m.head(m_var); } 
    public:
        use_list(emonomials const& m, lpvar v): m(m), m_var(v) {}
        iterator begin() { return iterator(m, head(), false); }
        iterator end() { return iterator(m, head(), true); }
    };

    use_list get_use_list(lpvar v) const { return use_list(*this, v); }

    /**
       \brief retrieve monomials m' where m is a proper factor of modulo current equalities.
    */
    class pf_iterator {
        emonomials const& m_em;
        monomial *   m_mon; // monomial
        iterator          m_it;  // iterator over the first variable occurs list, ++ filters out elements that do not have m as a factor
        iterator          m_end;

        void fast_forward();
    public:
        pf_iterator(emonomials const& m, monomial& mon, bool at_end);
        pf_iterator(emonomials const& m, lpvar v, bool at_end);
        monomial & operator*() {
            return *m_it;
        }
        pf_iterator& operator++() { ++m_it; fast_forward(); return *this; }
        pf_iterator operator++(int) { pf_iterator tmp = *this; ++*this; return tmp; }
        bool operator==(pf_iterator const& other) const { return m_it == other.m_it; }
        bool operator!=(pf_iterator const& other) const { return m_it != other.m_it; }
    };

    class products_of {
        emonomials const& m;
        monomial * mon;
        lpvar           m_var;
    public:
        products_of(emonomials const& m, monomial & mon): m(m), mon(&mon), m_var(UINT_MAX) {}
        products_of(emonomials const& m, lpvar v): m(m), mon(nullptr), m_var(v) {}
        pf_iterator begin() { if (mon) return pf_iterator(m, *mon, false); return pf_iterator(m, m_var, false); }
        pf_iterator end() { if (mon) return pf_iterator(m, *mon, true); return pf_iterator(m, m_var, true); }
    };

    products_of get_products_of(monomial& m) const { inc_visited(); return products_of(*this, m); }
    products_of get_products_of(lpvar v) const { inc_visited(); return products_of(*this, v); }
       
    monomial const* find_canonical(svector<lpvar> const& vars) const;

    /**
       \brief iterator over sign equivalent monomials.
       These are monomials that are equivalent modulo m_var_eqs amd modulo signs.
    */
    class sign_equiv_monomials_it {
        emonomials const& m;
        unsigned          m_index;
        bool              m_touched;
    public:
        sign_equiv_monomials_it(emonomials const& m, unsigned idx, bool at_end): 
            m(m), m_index(idx), m_touched(at_end) {}

        monomial const& operator*() { return m.m_monomials[m_index]; }

        sign_equiv_monomials_it& operator++() { 
            m_touched = true; 
            m_index = m.m_monomials[m_index].next(); 
            return *this; 
        }

        sign_equiv_monomials_it operator++(int) { 
            sign_equiv_monomials_it tmp = *this; 
            ++*this; 
            return tmp; 
        }

        bool operator==(sign_equiv_monomials_it const& other) const { 
            return m_index == other.m_index && m_touched == other.m_touched; 
        }

        bool operator!=(sign_equiv_monomials_it const& other) const { 
            return m_index != other.m_index || m_touched != other.m_touched; 
        }
    };

    class sign_equiv_monomials {
        const emonomials&     em;
        monomial const& m;
        unsigned index() const { return em.m_var2index[m.var()]; }
    public:
        sign_equiv_monomials(const emonomials & em, monomial const& m): em(em), m(m) {}
        sign_equiv_monomials_it begin() { return sign_equiv_monomials_it(em, index(), false); }
        sign_equiv_monomials_it end() { return sign_equiv_monomials_it(em, index(), true); }
    };

    sign_equiv_monomials enum_sign_equiv_monomials(monomial const& m) const { return sign_equiv_monomials(*this, m); }
    sign_equiv_monomials enum_sign_equiv_monomials(lpvar v) { return enum_sign_equiv_monomials((*this)[v]); }
    /**
       \brief display state of emonomials
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

    bool is_monomial_var(lpvar v) const { return m_var2index.get(v, UINT_MAX) != UINT_MAX; }
};

struct pp_emons {
    const core&       m_c;
    const emonomials& m_em;
    pp_emons(const core& c, const emonomials& e): m_c(c), m_em(e) {}
    inline std::ostream& display(std::ostream& out) const {
        return m_em.display(m_c, out);
    }
};

inline std::ostream& operator<<(std::ostream& out, pp_emons const& p) { return p.display(out); }

}
