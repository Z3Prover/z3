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
#include "math/lp/nla_defs.h"
#include "util/rational.h"
#include "math/lp/explanation.h"
#include "math/lp/incremental_vector.h"

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

template <typename T>
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

    T*                                m_merge_handler;    
    union_find<var_eqs>               m_uf;
    lp::incremental_vector<std::pair<signed_var, signed_var>>    
	                                  m_trail;
    vector<svector<eq_edge>>          m_eqs;    // signed_var.index() -> the edges adjacent to signed_var.index()

    trail_stack<var_eqs>              m_stack;
    mutable svector<var_frame>        m_todo;
    mutable svector<bool>             m_marked;
    mutable unsigned_vector           m_marked_trail;
    mutable svector<eq_justification> m_justtrail;
        
    mutable stats m_stats;
public:    
    var_eqs(): m_merge_handler(nullptr), m_uf(*this), m_stack(*this) {}    
    /**
       \brief push a scope    */
    void push() {
        m_trail.push_scope();
        m_stack.push_scope();
    }

    /**
       \brief pop n scopes
    */
    void pop(unsigned n)  {
        unsigned old_sz = m_trail.peek_size(n);
        for (unsigned i = m_trail.size(); i-- > old_sz; ) {
            auto const& sv = m_trail[i];
            m_eqs[sv.first.index()].pop_back();
            m_eqs[sv.second.index()].pop_back();
            m_eqs[(~sv.first).index()].pop_back();
            m_eqs[(~sv.second).index()].pop_back();
        }
        m_trail.pop_scope(n);
        m_stack.pop_scope(n); // this cass takes care of unmerging through union_find m_uf
    }

    /**
       \brief merge equivalence classes for v1, v2 with justification j
    */
    void merge(signed_var v1, signed_var v2, eq_justification const& j)  {
        unsigned max_i = std::max(v1.index(), v2.index()) + 2;
        m_eqs.reserve(max_i);
        while (m_uf.get_num_vars() <= max_i) m_uf.mk_var();
        m_trail.push_back(std::make_pair(v1, v2));
        m_uf.merge(v1.index(), v2.index());
        m_uf.merge((~v1).index(), (~v2).index());
        m_eqs[v1.index()].push_back(eq_edge(v2, j));
        m_eqs[v2.index()].push_back(eq_edge(v1, j));
        m_eqs[(~v1).index()].push_back(eq_edge(~v2, j));
        m_eqs[(~v2).index()].push_back(eq_edge(~v1, j));
    }

    void merge_plus(lpvar v1, lpvar v2, eq_justification const& j)  { merge(signed_var(v1, false), signed_var(v2, false), j); }
    void merge_minus(lpvar v1, lpvar v2, eq_justification const& j) { merge(signed_var(v1, false), signed_var(v2, true),  j); }

    /**
       \brief find equivalence class representative for v
    */
    signed_var find(signed_var v) const {
        if (v.index() >= m_uf.get_num_vars()) {
            return v;
        }
        unsigned idx = m_uf.find(v.index());
        return signed_var(idx);
    }
    
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
    void explain_dfs(signed_var v1, signed_var v2, lp::explanation& e) const {
        SASSERT(find(v1) == find(v2));
        if (v1 == v2) {
            return;
        }
        m_todo.push_back(var_frame(v1, 0));
        m_justtrail.reset();
        m_marked.reserve(m_eqs.size(), false);
        SASSERT(m_marked_trail.empty());
        m_marked[v1.index()] = true;
        m_marked_trail.push_back(v1.index());
        while (true) {
            SASSERT(!m_todo.empty());
            var_frame& f = m_todo.back();
            signed_var v = f.m_var;
            if (v == v2) {
                break;
            }
            auto const& next = m_eqs[v.index()];
            bool seen_all = true;
            unsigned sz = next.size();
            for (unsigned i = f.m_index; seen_all && i < sz; ++i) {
                eq_edge const& jv = next[i];
                signed_var v3 = jv.m_var;
                if (!m_marked[v3.index()]) {
                    seen_all = false;
                    f.m_index = i + 1;
                    m_todo.push_back(var_frame(v3, 0));
                    m_justtrail.push_back(jv.m_just);
                    m_marked_trail.push_back(v3.index());
                    m_marked[v3.index()] = true;
                }
            }
            if (seen_all) {
                m_todo.pop_back();
                m_justtrail.pop_back();
            }
        }
        
        for (eq_justification const& j : m_justtrail) {
            j.explain(e);
        }
        m_stats.m_num_explains += m_justtrail.size();
        m_stats.m_num_explain_calls++;
        m_todo.reset();
        m_justtrail.reset();
        for (unsigned idx : m_marked_trail) {
            m_marked[idx] = false;
        }
        m_marked_trail.reset();

        // IF_VERBOSE(2, verbose_stream() << (double)m_stats.m_num_explains / m_stats.m_num_explain_calls << "\n");
    }

    void explain_bfs(signed_var v1, signed_var v2, lp::explanation& e) const {
        SASSERT(find(v1) == find(v2));
        if (v1 == v2) {
            return;
        }
        m_todo.push_back(var_frame(v1, 0));
        m_justtrail.push_back(eq_justification({}));
        m_marked.reserve(m_eqs.size(), false);
        SASSERT(m_marked_trail.empty());
        m_marked[v1.index()] = true;
        m_marked_trail.push_back(v1.index());
        unsigned head = 0;
        for (; ; ++head) {
            var_frame& f = m_todo[head];
            signed_var v = f.m_var;
            if (v == v2) {
                break;
            }
            auto const& next = m_eqs[v.index()];
            unsigned sz = next.size();
            for (unsigned i = sz; i-- > 0; ) {
                eq_edge const& jv = next[i];
                signed_var v3 = jv.m_var;
                if (!m_marked[v3.index()]) {
                    m_todo.push_back(var_frame(v3, head));
                    m_justtrail.push_back(jv.m_just);
                    m_marked_trail.push_back(v3.index());
                    m_marked[v3.index()] = true;
                }
            }
        }
        
        while (head != 0) {
            m_justtrail[head].explain(e);
            head = m_todo[head].m_index;
            ++m_stats.m_num_explains;
        }
        ++m_stats.m_num_explain_calls;
        
        m_todo.reset();
        m_justtrail.reset();
        for (unsigned idx : m_marked_trail) {
            m_marked[idx] = false;
        }
        m_marked_trail.reset();

        // IF_VERBOSE(2, verbose_stream() << (double)m_stats.m_num_explains / m_stats.m_num_explain_calls << "\n");
    }


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


    std::ostream& display(std::ostream& out) const {
        m_uf.display(out);
        unsigned idx = 0;
        for (auto const& edges : m_eqs) {
            if (!edges.empty()) {
                auto v = signed_var(idx);
                out << v << " root: " << find(v) << " : ";
                for (auto const& jv : edges) {
                    out << jv.m_var << " ";
                }
                out << "\n";
            }
            ++idx;
        }
        return out;
    }

    // union find event handlers
    void set_merge_handler(T* mh) { m_merge_handler = mh; }
    // this method is required by union_find
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
};  // end of var_eqs
}
