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
#include "ast/sls/sls_valuation.h"
#include "ast/sls/sls_smt.h"

namespace bv {

    class sls_terms {
        sls::context&       ctx;
        ast_manager&        m;
        bv_util             bv;
        expr_ref_vector     m_translated;
        ptr_vector<expr>    m_subterms;

        void ensure_binary(expr* e);

        expr_ref mk_sdiv(expr* x, expr* y);
        expr_ref mk_smod(expr* x, expr* y);
        expr_ref mk_srem(expr* x, expr* y);

    public:
        sls_terms(sls::context& ctx);       

        /**
         * Initialize structures: assertions, parents, terms
         */        
        void init();

        expr* translated(expr* e) const { return m_translated.get(e->get_id(), nullptr); }

        ptr_vector<expr> const& subterms() const { return m_subterms; }

    };
}
