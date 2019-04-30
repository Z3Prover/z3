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

#include "util/lp/var_eqs.h"

namespace nla {
    

var_eqs::var_eqs(): m_merge_handler(nullptr), m_uf(*this), m_stack(*this) {}
    
void var_eqs::push() {
    m_trail_lim.push_back(m_trail.size());
    get_trail_stack().push_scope();
}

void var_eqs::pop(unsigned n) {
    unsigned old_sz = m_trail_lim[m_trail_lim.size() - n];
    for (unsigned i = m_trail.size(); i-- > old_sz; ) {
        auto const& sv = m_trail[i];
        m_eqs[sv.first.index()].pop_back();
        m_eqs[sv.second.index()].pop_back();
        m_eqs[(~sv.first).index()].pop_back();
        m_eqs[(~sv.second).index()].pop_back();
    }
    m_trail_lim.shrink(m_trail_lim.size() - n);
    m_trail.shrink(old_sz);
    get_trail_stack().pop_scope(n);
}

void var_eqs::merge(signed_var v1, signed_var v2, eq_justification const& j) {
    unsigned max_i = std::max(v1.index(), v2.index()) + 2;
    m_eqs.reserve(max_i);
    while (m_uf.get_num_vars() <= max_i) m_uf.mk_var();
    m_trail.push_back(std::make_pair(v1, v2));
    m_uf.merge(v1.index(), v2.index());
    m_uf.merge((~v1).index(), (~v2).index());
    m_eqs[v1.index()].push_back(justified_var(v2, j));
    m_eqs[v2.index()].push_back(justified_var(v1, j));
    m_eqs[(~v1).index()].push_back(justified_var(~v2, j));
    m_eqs[(~v2).index()].push_back(justified_var(~v1, j));
}

signed_var var_eqs::find(signed_var v) const {
    if (v.index() >= m_uf.get_num_vars()) {
        return v;
    }
    unsigned idx = m_uf.find(v.index());
    return signed_var(idx, from_index_dummy());
}

void var_eqs::explain_dfs(signed_var v1, signed_var v2, lp::explanation& e) const {
    SASSERT(find(v1) == find(v2));
    if (v1 == v2) {
        return;
    }
    m_todo.push_back(var_frame(v1, 0));
    m_jtrail.reset();
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
            justified_var const& jv = next[i];
            signed_var v3 = jv.m_var;
            if (!m_marked[v3.index()]) {
                seen_all = false;
                f.m_index = i + 1;
                m_todo.push_back(var_frame(v3, 0));
                m_jtrail.push_back(jv.m_j);
                m_marked_trail.push_back(v3.index());
                m_marked[v3.index()] = true;
            }
        }
        if (seen_all) {
            m_todo.pop_back();
            m_jtrail.pop_back();
        }
    }
        
    for (eq_justification const& j : m_jtrail) {
        j.explain(e);
    }
    m_stats.m_num_explains += m_jtrail.size();
    m_stats.m_num_explain_calls++;
    m_todo.reset();
    m_jtrail.reset();
    for (unsigned idx : m_marked_trail) {
        m_marked[idx] = false;
    }
    m_marked_trail.reset();

    // IF_VERBOSE(2, verbose_stream() << (double)m_stats.m_num_explains / m_stats.m_num_explain_calls << "\n");
}

void var_eqs::explain_bfs(signed_var v1, signed_var v2, lp::explanation& e) const {
    SASSERT(find(v1) == find(v2));
    if (v1 == v2) {
        return;
    }
    m_todo.push_back(var_frame(v1, 0));
    m_jtrail.push_back(eq_justification({}));
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
            justified_var const& jv = next[i];
            signed_var v3 = jv.m_var;
            if (!m_marked[v3.index()]) {
                m_todo.push_back(var_frame(v3, head));
                m_jtrail.push_back(jv.m_j);
                m_marked_trail.push_back(v3.index());
                m_marked[v3.index()] = true;
            }
        }
    }
        
    while (head != 0) {
        m_jtrail[head].explain(e);
        head = m_todo[head].m_index;
        ++m_stats.m_num_explains;
    }
    ++m_stats.m_num_explain_calls;
        
    m_todo.reset();
    m_jtrail.reset();
    for (unsigned idx : m_marked_trail) {
        m_marked[idx] = false;
    }
    m_marked_trail.reset();

    // IF_VERBOSE(2, verbose_stream() << (double)m_stats.m_num_explains / m_stats.m_num_explain_calls << "\n");
}


std::ostream& var_eqs::display(std::ostream& out) const {
    m_uf.display(out);
    unsigned idx = 0;
    for (auto const& edges : m_eqs) {
        if (!edges.empty()) {
            auto v = signed_var(idx, from_index_dummy());
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

}
