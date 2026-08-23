/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    bv_slice.h

Abstract:

    simplifier for extracting bit-vector ranges
    It rewrites a state using bit-vector slices. 
    Slices are extracted from bit-vector equality assertions 
    in the style of (but not fully implementing a full slicing) 
    Bjorner & Pichora, TACAS 1998 and Brutomesso et al 2008.

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-2.

--*/


#pragma once

#include "util/uint_set.h"
#include "ast/bv_decl_plugin.h"
#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/rewriter/th_rewriter.h"


namespace bv {

    class slice : public dependent_expr_simplifier {
        bv_util                 m_bv;
        th_rewriter             m_rewriter;
        obj_map<expr, uint_set> m_boundaries;
        ptr_vector<expr>        m_xs, m_ys;
        
        expr* mk_extract(unsigned hi, unsigned lo, expr* x);
        void process_eqs();
        void process_eq(expr* e);
        void slice_eq();
        void register_slice(unsigned lo, unsigned hi, expr* x);     
        void apply_subst();
        void get_concats(expr* x, ptr_vector<expr>& xs);
        
    public:

        slice(ast_manager& m, dependent_expr_state& fmls) : dependent_expr_simplifier(m, fmls), m_bv(m), m_rewriter(m) {}
        char const* name() const override { return "bv-slice"; }
        void push() override { dependent_expr_simplifier::push(); }
        void pop(unsigned n) override { dependent_expr_simplifier::pop(n); }
        void reduce() override;
    };
}
