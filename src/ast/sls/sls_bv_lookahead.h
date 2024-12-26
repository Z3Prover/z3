/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_bv_lookahead.h

Abstract:

    Lookahead solver for BV, modeled after sls_engine/sls_tracker/sls_evaluator.

Author:

    Nikolaj Bjorner (nbjorner) 2024-12-26

--*/
#pragma once

#include "ast/bv_decl_plugin.h"
#include "ast/sls/sls_context.h"

namespace sls {
    class bv_eval;
    class bv_valuation;
    class bvect;

    class bv_lookahead {
        bv_util bv;
        bv_eval& m_ev;
        context& ctx;
        ast_manager& m;

        ptr_vector<expr> m_restore;
        vector<ptr_vector<expr>> m_update_stack;
        expr_mark m_on_restore;

        bv_valuation& wval(expr* e) const;

        void insert_update_stack(expr* e);
        bool insert_update(expr* e);
        
        void restore_lookahead();

        double lookahead(expr* e, bvect const& new_value);

    public:
        bv_lookahead(bv_eval& ev);
        bool on_restore(expr* e) const;

        bool try_repair_down(expr* e);

    };
}