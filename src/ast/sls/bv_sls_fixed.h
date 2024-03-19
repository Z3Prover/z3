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
#include "ast/sls/sls_valuation.h"
#include "ast/bv_decl_plugin.h"

namespace bv {

    class sls_eval;
    
    class sls_fixed {
        sls_eval&           ev;
        ast_manager&        m;
        bv_util&            bv;

        void init_ranges(expr_ref_vector const& es);
        void init_range(app* e, bool sign);
        void init_range(expr* x, rational const& a, expr* y, rational const& b, bool sign);
        void get_offset(expr* e, expr*& x, rational& offset);

        void init_fixed_basic(app* e);
        void init_fixed_bv(app* e);

        bool is_fixed1(app* e) const;
        bool is_fixed1_basic(app* e) const;
        void set_fixed_bw(app* e);

        sls_valuation& wval(expr* e);

    public:
        sls_fixed(sls_eval& ev);

        void init(expr_ref_vector const& es);

    };
}
