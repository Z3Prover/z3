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
#include "util/params.h"
#include "util/scoped_ptr_vector.h"
#include "util/uint_set.h"
#include "ast/ast.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/sls/sls_stats.h"
#include "ast/sls/sls_powers.h"
#include "ast/sls/sls_valuation.h"
#include "ast/bv_decl_plugin.h"

namespace bv {

    class sls_terms {
        ast_manager&        m;
        bv_util             bv;
        th_rewriter         m_rewriter;
        ptr_vector<expr>    m_todo, m_args;
        expr_ref_vector     m_assertions, m_pinned, m_translated;
        app_ref_vector      m_terms;
        vector<ptr_vector<expr>> m_parents;
        tracked_uint_set    m_assertion_set;

        expr* ensure_binary(expr* e);
        void ensure_binary_core(expr* e);

        expr_ref mk_sdiv(expr* x, expr* y);
        expr_ref mk_smod(expr* x, expr* y);
        expr_ref mk_srem(expr* x, expr* y);

    public:
        sls_terms(ast_manager& m);

        void updt_params(params_ref const& p);
        
        /**
        * Add constraints
        */
        void assert_expr(expr* e);

        /**
         * Initialize structures: assertions, parents, terms
         */        
        void init();

        /**
         * Accessors.
         */
        
        ptr_vector<expr> const& parents(expr* e) const { return m_parents[e->get_id()]; }

        expr_ref_vector const& assertions() const { return m_assertions; }

        app* term(unsigned id) const { return m_terms.get(id); }

        app_ref_vector const& terms() const { return m_terms; }

        bool is_assertion(expr* e) const { return m_assertion_set.contains(e->get_id()); }

    };
}
