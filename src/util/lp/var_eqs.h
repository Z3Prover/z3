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
    
typedef lp::var_index lpvar;
typedef lp::constraint_index lpci;
struct from_index{};

class signed_var {
    unsigned m_sv;
public:
    // constructor, sign = true means minus
    signed_var(lpvar v, bool sign): m_sv((v << 1) + (sign ? 1 : 0)) {}
    // constructor
    signed_var(unsigned sv, from_index): m_sv(sv) {}
    bool sign() const { return 0 != (m_sv & 0x1); }
    lpvar var() const { return m_sv >> 1; }
    unsigned index() const { return m_sv; }        
    void neg() { m_sv = m_sv ^ 1; }
    friend signed_var operator~(signed_var const& sv) {
        return signed_var(sv.var(), !sv.sign());
    }
    bool operator==(signed_var const& other) const {
        return m_sv == other.m_sv;
    }
    bool operator!=(signed_var const& other) const {
        return m_sv != other.m_sv;
    }
    rational rsign() const { return sign() ? rational::minus_one() : rational::one(); }

    std::ostream& display(std::ostream& out) const {
        return out << (sign()?"-":"") << var();
    }
};

    inline std::ostream& operator<<(std::ostream& out, signed_var const& sv) {
        return sv.display(out);
    }

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

class var_eqs {
    struct justified_var {
        signed_var       m_var;
        eq_justification m_j;
        justified_var(signed_var v, eq_justification const& j): m_var(v), m_j(j) {}
    };
    typedef svector<justified_var> justified_vars;

    struct dfs_frame {
        signed_var m_var;
        unsigned   m_index;
        dfs_frame(signed_var v, unsigned i): m_var(v), m_index(i) {}
    };
    typedef std::pair<signed_var, signed_var> signed_var_pair;

    union_find_default_ctx  m_ufctx;
    union_find<>            m_uf;
    svector<signed_var_pair>    m_trail;
    unsigned_vector         m_trail_lim;
    vector<justified_vars>  m_eqs;    // signed_var-index -> justified_var corresponding to edges in a graph used to extract justifications.

    mutable svector<dfs_frame>      m_todo;
    mutable svector<bool>           m_marked;
    mutable unsigned_vector         m_marked_trail;
    mutable svector<eq_justification> m_dfs_trail;
        
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
    bool vars_are_equiv(lpvar j, lpvar k) const {
        signed_var sj = find(signed_var(j, false));
        signed_var sk = find(signed_var(k, false));
        return sj.var() == sk.var();
    }
    /**
       \brief Returns eq_justifications for
       \pre find(v1) == find(v2)
    */
    void explain(signed_var v1, signed_var v2, lp::explanation& e) const;
    inline 
    void explain(lpvar v1, lpvar v2, lp::explanation & e) const {
        return explain(signed_var(v1, false), signed_var(v2, false), e);
    }

    inline void explain(lpvar j, lp::explanation& e) const {
        signed_var s(j, false);
        return explain(find(s), s, e); 
    }

    class iterator {
        var_eqs& m_ve;        // context.
        unsigned m_idx;       // index into a signed variable, same as union-find index
        bool     m_touched;   // toggle between initial and final state
    public:
        iterator(var_eqs& ve, unsigned idx, bool t) : m_ve(ve), m_idx(idx), m_touched(t) {}
        signed_var operator*() const {
            return signed_var(m_idx, from_index()); // 0 is needed to call the right constructor
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
}; 
}
