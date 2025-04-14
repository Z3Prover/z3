/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    bv_sls_fixed.h

Abstract:

    Initialize fixed information.

Author:

    Nikolaj Bjorner (nbjorner) 2024-02-07
    
--*/
#pragma once

#include "ast/ast.h"
#include "ast/sls/sls_bv_valuation.h"
#include "ast/sls/sls_context.h"
#include "ast/bv_decl_plugin.h"


namespace sls {

    class bv_terms;
    class bv_eval;
    
    class bv_fixed {
        bv_eval&        ev;
        ast_manager&    m;
        bv_util&        bv;
        sls::context&   ctx;

        bool init_range(app* e, bool sign);
        void propagate_range_up(expr* e);
        bool init_range(expr* x, rational const& a, expr* y, rational const& b, bool sign);
        void get_offset(expr* e, expr*& x, rational& offset);
        bool init_eq(expr* e, rational const& v, bool sign);
        bool add_range(expr* e, rational lo, rational hi, bool sign);

        bool is_fixed1(app* e) const;
        void set_fixed(expr* e);

    public:
        bv_fixed(bv_eval& ev, bv_terms& terms, sls::context& ctx);
        void init();
    };
}
