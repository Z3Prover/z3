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
    

    var_eqs::var_eqs(): m_uf(m_ufctx) {}
    
    void var_eqs::push() {
        m_trail_lim.push_back(m_trail.size());
        m_ufctx.get_trail_stack().push_scope();
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
        m_trail_lim.shrink(n);
        m_trail.shrink(old_sz);
        m_ufctx.get_trail_stack().pop_scope(n);
    }

    void var_eqs::merge(signed_var v1, signed_var v2, eq_justification const& j) {
        unsigned max_i = std::max(v1.index(), v2.index()) + 1;
        m_eqs.reserve(max_i);
        while (m_uf.get_num_vars() <= max_i) m_uf.mk_var();
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
        return signed_var(idx);
    }

    void var_eqs::explain(signed_var v1, signed_var v2, lp::explanation& e) const {
    SASSERT(find(v1) == find(v2));
        unsigned_vector ret;
        if (v1 == v2) {
            return;
        }
        m_todo.push_back(dfs_frame(v1, 0));
        m_dfs_trail.reset();
        m_marked.reserve(m_eqs.size(), false);
        SASSERT(m_marked_trail.empty());
        while (true) {
            SASSERT(!m_todo.empty());
            dfs_frame& f = m_todo.back();
            signed_var v = f.m_var;
            if (v == v2) {
                break;
            }
            auto const& next = m_eqs[v.index()];
            unsigned sz = next.size();
            bool seen_all = true;
            for (unsigned i = f.m_index; !seen_all && i < sz; ++i) {
                justified_var const& jv = next[i];
                if (!m_marked[jv.m_var.index()]) {
                    seen_all = false;
                    f.m_index = i + 1;
                    m_todo.push_back(dfs_frame(jv.m_var, 0));
                    m_dfs_trail.push_back(jv.m_j);
                    m_marked[jv.m_var.index()] = true;
                }
            }
            if (seen_all) {
                m_todo.pop_back();
                m_dfs_trail.pop_back();
            }
        }
        
        for (eq_justification const& j : m_dfs_trail) {
            j.explain(e);
        }
        m_dfs_trail.reset();
        for (unsigned idx : m_marked_trail) {
            m_marked[idx] = false;
        }
        m_marked_trail.reset();
    }

}
