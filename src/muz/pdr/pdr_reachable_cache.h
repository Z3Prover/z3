/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    reachable_cache.h

Abstract:

    Object for caching of reachable states.

Author:

    Krystof Hoder (t-khoder) 2011-9-14.

Revision History:

--*/


#ifndef REACHABLE_CACHE_H_
#define REACHABLE_CACHE_H_
#include "ast.h"
#include "ref_vector.h"
#include "pdr_manager.h"
#include "pdr_smt_context_manager.h"

namespace pdr {
    class reachable_cache {
        struct stats {
            unsigned             m_hits;
            unsigned             m_miss;
            unsigned             m_inserts;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };

        ast_manager &        m;
        manager &            m_pm;
        scoped_ptr<smt_context>    m_ctx;
        ast_ref_vector       m_ref_holder;
        app_ref              m_disj_connector;
        obj_hashtable<expr>  m_cache;
        stats                m_stats;
        datalog::PDR_CACHE_MODE m_cache_mode;
        
        void add_disjuncted_formula(expr * f);
        
    public:
        reachable_cache(pdr::manager & pm, datalog::PDR_CACHE_MODE cm);
        
        void add_init(app * f)   { add_disjuncted_formula(f); }
        
        /** add cube whose all models are reachable */
        void add_reachable(expr * cube);
        
        /** return true if there is a model of cube which is reachable */
        bool is_reachable(expr * cube);
        
        void collect_statistics(statistics& st) const;

        void reset_statistics();
    };
}

#endif
