/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    reachable_cache.cpp

Abstract:

    Object for caching of reachable states.

Author:

    Krystof Hoder (t-khoder) 2011-9-14.

Revision History:

--*/

#include "muz/pdr/pdr_reachable_cache.h"

namespace pdr {

    reachable_cache::reachable_cache(pdr::manager & pm, datalog::PDR_CACHE_MODE cm)
        : m(pm.get_manager()), 
          m_pm(pm), 
          m_ctx(nullptr),
          m_ref_holder(m), 
          m_disj_connector(m),
          m_cache_mode(cm) {
        if (m_cache_mode == datalog::CONSTRAINT_CACHE) {
            m_ctx = pm.mk_fresh();
            m_ctx->assert_expr(m_pm.get_background());
        }
    }
    
    
    void reachable_cache::add_disjuncted_formula(expr * f) {
        app_ref new_connector(m.mk_fresh_const("disj_conn", m.mk_bool_sort()), m);
        app_ref neg_new_connector(m.mk_not(new_connector), m);
        app_ref extended_form(m);
        
        if(m_disj_connector) {
            extended_form = m.mk_or(m_disj_connector, neg_new_connector, f);
        }
        else {
            extended_form = m.mk_or(neg_new_connector, f);
        }
        if (m_ctx) {
            m_ctx->assert_expr(extended_form);
        }
        
        m_disj_connector = new_connector;
    }
    
    void reachable_cache::add_reachable(expr * cube) {
        
        switch (m_cache_mode) {
        case datalog::NO_CACHE: 
            break;
            
        case datalog::HASH_CACHE: 
            m_stats.m_inserts++;
            m_cache.insert(cube);
            m_ref_holder.push_back(cube);
            break;
            
        case datalog::CONSTRAINT_CACHE: 
            m_stats.m_inserts++;
            TRACE("pdr", tout << mk_pp(cube, m) << "\n";);
            add_disjuncted_formula(cube);
            break;
            
        default:
            UNREACHABLE();        
        }
    }

    bool reachable_cache::is_reachable(expr * cube) {
        bool found = false;
        switch (m_cache_mode) {
        case datalog::NO_CACHE: 
            return false;

        case datalog::HASH_CACHE: 
            found = m_cache.contains(cube);
            break;

        case datalog::CONSTRAINT_CACHE: {        
            if(!m_disj_connector) {
                found = false;
                break;
            }
            expr * connector = m_disj_connector.get();
            expr_ref_vector assms(m);
            assms.push_back(connector);
            m_ctx->push();
            m_ctx->assert_expr(cube);
            lbool res = m_ctx->check(assms);
            m_ctx->pop();
               
            TRACE("pdr", tout << "is_reachable: " << res << " " << mk_pp(cube, m) << "\n";);

            found = res == l_true;
            break;
        }

        default:
            UNREACHABLE();
            break;
        }
        if (found) {
            m_stats.m_hits++; 
        }
        else {
            m_stats.m_miss++;
        }
        return found;
    }

    void reachable_cache::collect_statistics(statistics& st) const {
        st.update("cache inserts", m_stats.m_inserts);
        st.update("cache miss", m_stats.m_miss);
        st.update("cache hits", m_stats.m_hits);
    }

    void reachable_cache::reset_statistics() {
        m_stats.reset();
    }


}
