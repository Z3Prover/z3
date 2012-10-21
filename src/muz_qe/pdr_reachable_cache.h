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

#include "ast.h"
#include "params.h"
#include "ref_vector.h"
#include "pdr_manager.h"
#include "pdr_smt_context_manager.h"

#ifndef _REACHABLE_CACHE_H_
#define _REACHABLE_CACHE_H_

namespace pdr {
    class reachable_cache {
        ast_manager &        m;
        manager &            m_pm;
        scoped_ptr<smt_context>    m_ctx;
        ast_ref_vector       m_ref_holder;
        app_ref              m_disj_connector;
        obj_hashtable<expr>  m_cache;
        unsigned             m_cache_hits;
        unsigned             m_cache_miss;
        unsigned             m_cache_inserts;
        datalog::PDR_CACHE_MODE m_cache_mode;
        
        void add_disjuncted_formula(expr * f);
        
    public:
        reachable_cache(pdr::manager & pm, params_ref const& params);
        
        void add_init(app * f)   { add_disjuncted_formula(f); }
        
        /** add cube whose all models are reachable */
        void add_reachable(expr * cube);
        
        /** return true if there is a model of cube which is reachable */
        bool is_reachable(expr * cube);
        
        void collect_statistics(statistics& st) const;
    };
}

#endif
