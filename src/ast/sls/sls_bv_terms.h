/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    bv_sls_terms.h

Abstract:

    A Stochastic Local Search (SLS) engine

Author:

    Nikolaj Bjorner (nbjorner) 2024-02-07
    
--*/
#pragma once

#include "util/lbool.h"
#include "util/scoped_ptr_vector.h"
#include "util/uint_set.h"
#include "ast/ast.h"
#include "ast/bv_decl_plugin.h"
#include "ast/sls/sls_stats.h"
#include "ast/sls/sls_powers.h"
#include "ast/sls/sls_bv_valuation.h"
#include "ast/sls/sls_context.h"

namespace sls {

    class bv_terms {
        ast_manager&        m;
        bv_util             bv;
        expr_ref_vector     m_axioms;
        vector<ptr_vector<expr>> m_uninterp_occurs;

        expr_ref ensure_binary(expr* e);

        expr_ref mk_sdiv(expr* x, expr* y);
        expr_ref mk_smod(expr* x, expr* y);
        expr_ref mk_srem(expr* x, expr* y);

        void register_uninterp(expr* e);

    public:
        bv_terms(context& ctx);       

        void register_term(expr* e);

        bool is_bv_predicate(expr* e) const;

        expr_ref_vector& axioms() { return m_axioms; }

        ptr_vector<expr> const& uninterp_occurs(expr* e);
    };
}
