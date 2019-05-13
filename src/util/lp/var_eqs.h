/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  <name>

  Abstract:

  <abstract>

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  Revision History:


  --*/

#pragma once
#include "util/union_find.h"
#include "util/lp/lp_types.h"
#include "util/rational.h"
#include "util/lp/explanation.h"
namespace nla {

class eq_justification {
    lpci m_cs[4];
public:
    eq_justification(std::initializer_list<lpci> cs) {
        int i = 0;
        for (lpci c: cs) {
            m_cs[i++] = c;
        }
        for (; i < 4; i++) {
            m_cs[i] = -1;
        }
    }

    void explain(lp::explanation& e) const {
        for (lpci c : m_cs)
            if (c + 1 != 0) // c != -1
                e.add(c);
    }
};

class var_eqs_merge_handler {
public:
    virtual void merge_eh(signed_var r2, signed_var r1, signed_var v2, signed_var v1) = 0;
    virtual void after_merge_eh(signed_var r2, signed_var r1, signed_var v2, signed_var v1) = 0;
    virtual void unmerge_eh(signed_var r2, signed_var r1) = 0;
};

class var_eqs {
    struct eq_edge {
        signed_var       m_var;
        eq_justification m_just;
        eq_edge(signed_var v, eq_justification const& j): m_var(v), m_just(j) {}
    };

    struct var_frame {
        signed_var m_var;
        unsigned   m_index;
        var_frame(signed_var v, unsigned i): m_var(v), m_index(i) {}
    };
    struct stats {
        unsigned m_num_explain_calls;
        unsigned m_num_explains;
        stats() { memset(this, 0, sizeof(*this)); }
    };

    var_eqs_merge_handler*  m_merge_handler;    
    union_find<var_eqs>         m_uf;
    svector<std::pair<signed_var, signed_var>>    m_trail;
    unsigned_vector            m_trail_lim;
    vector<svector<eq_edge>>   m_eqs;    // signed_var.index() -> the edges adjacent to signed_var.index()

    trail_stack<var_eqs>             m_stack;
    mutable svector<var_frame>      m_todo;
    mutable svector<bool>           m_marked;
    mutable unsigned_vector         m_marked_trail;
    mutable svector<eq_justification> m_justtrail;
        
    mutable stats m_stats;
public:
    var_eqs();
    
    /**
       \brief push a scope
    */
    void push();

    /**
       \brief pop n scopes
    */
    void pop(unsigned n);

    /**
       \brief merge equivalence classes for v1, v2 with justification j
    */
    void merge(signed_var v1, signed_var v2, eq_justification const& j);
    void merge_plus(lpvar v1, lpvar v2, eq_justification const& j)  { merge(signed_var(v1, false), signed_var(v2, false), j); }
    void merge_minus(lpvar v1, lpvar v2, eq_justification const& j) { merge(signed_var(v1, false), signed_var(v2, true),  j); }

    /**
       \brief find equivalence class representative for v
    */
    signed_var find(signed_var v) const;
    
    inline signed_var find(lpvar j) const {
        return find(signed_var(j, false));        
    }

    inline bool is_root(lpvar j) const {
        signed_var sv = find(signed_var(j, false));
        return sv.var() == j;            
    }
    inline bool is_root(svector<lpvar> v) const {
        for (lpvar j : v)
            if (! is_root(j))
                return false;
        return true;
    }

    bool vars_are_equiv(lpvar j, lpvar k) const {
        signed_var sj = find(signed_var(j, false));
        signed_var sk = find(signed_var(k, false));
        return sj.var() == sk.var();
    }
    /**
       \brief Returns eq_justifications for
       \pre find(v1) == find(v2)
    */
    void explain_dfs(signed_var v1, signed_var v2, lp::explanation& e) const;
    void explain_bfs(signed_var v1, signed_var v2, lp::explanation& e) const;

    inline void explain(signed_var v1, signed_var v2, lp::explanation& e) const {
        explain_bfs(v1, v2, e);
    }
    inline void explain(lpvar v1, lpvar v2, lp::explanation & e) const {
        return explain(signed_var(v1, false), signed_var(v2, false), e);
    }

    inline void explain(lpvar j, lp::explanation& e) const {
        signed_var s(j, false);
        return explain(find(s), s, e); 
    }

    // iterates over the class of lpvar(m_idx)
    class iterator {
        var_eqs& m_ve;        // context.
        unsigned m_idx;       // index into a signed variable, same as union-find index
        bool     m_touched;   // toggle between initial and final state
    public:
        iterator(var_eqs& ve, unsigned idx, bool t) : m_ve(ve), m_idx(idx), m_touched(t) {}
        signed_var operator*() const {
            return signed_var(m_idx);
        }
        iterator& operator++() { m_idx = m_ve.m_uf.next(m_idx); m_touched = true; return *this; }
        bool operator==(iterator const& other) const { return m_idx == other.m_idx && m_touched == other.m_touched; }
        bool operator!=(iterator const& other) const { return m_idx != other.m_idx || m_touched != other.m_touched; }
    };

    class eq_class {
        var_eqs& m_ve;
        signed_var m_v;
    public:
        eq_class(var_eqs& ve, signed_var v) : m_ve(ve), m_v(v) {}
        iterator begin() { return iterator(m_ve, m_v.index(), false); }
        iterator end() { return iterator(m_ve, m_v.index(), true); }
    };

    eq_class equiv_class(signed_var v) { return eq_class(*this, v); }

    eq_class equiv_class(lpvar v) { return equiv_class(signed_var(v, false)); }


    std::ostream& display(std::ostream& out) const;

    // union find event handlers
    void set_merge_handler(var_eqs_merge_handler* mh) { m_merge_handler = mh; }
    trail_stack<var_eqs> & get_trail_stack() { return m_stack; }

    void unmerge_eh(unsigned i, unsigned j) { 
        if (m_merge_handler) {
            m_merge_handler->unmerge_eh(signed_var(i), signed_var(j)); 
        }
    }
    void merge_eh(unsigned r2, unsigned r1, unsigned v2, unsigned v1) {
        if (m_merge_handler) {
            m_merge_handler->merge_eh(signed_var(r2), signed_var(r1),
                                      signed_var(v2), signed_var(v1)); 
        }
    }

    void after_merge_eh(unsigned r2, unsigned r1, unsigned v2, unsigned v1) {
        if (m_merge_handler) {
            m_merge_handler->after_merge_eh(signed_var(r2), signed_var(r1),
                                            signed_var(v2), signed_var(v1)); 
        }
    }


}; 

    inline std::ostream& operator<<(var_eqs const& ve, std::ostream& out) { return ve.display(out); }
}
