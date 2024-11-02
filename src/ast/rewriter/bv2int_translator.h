/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    bv2int_translator
    Utilities for translating bit-vector constraints into arithmetic.
    
Author:

    Nikolaj Bjorner (nbjorner) 2024-10-27


--*/
#pragma once

#include "util/trail.h"

class bv2int_translator_trail {
public:
    virtual ~bv2int_translator_trail() {}
    virtual void push(push_back_vector<expr_ref_vector> const& c) = 0;
    virtual void push(push_back_vector<ptr_vector<app>> const& c) = 0;
    virtual void push_idx(set_vector_idx_trail<expr_ref_vector> const& c) = 0;
};

class bv2int_translator {
    ast_manager& m;
    bv2int_translator_trail& ctx;
    bv_util bv;
    arith_util a;
    obj_map<func_decl, func_decl*> m_new_funs;
    expr_ref_vector m_translate, m_args;
    ast_ref_vector m_pinned;
    ptr_vector<app> m_bv2int, m_int2bv;
    expr_ref_vector m_vars, m_preds;
    bool m_is_plugin = true;

    void set_translated(expr* e, expr* r);
    expr* arg(unsigned i) { return m_args.get(i); }
    
    expr* umod(expr* bv_expr, unsigned i);
    expr* smod(expr* bv_expr, unsigned i);
    bool is_bounded(expr* v, rational const& N);
    bool is_non_negative(expr* bv_expr, expr* e);
    expr_ref mul(expr* x, expr* y);
    expr_ref add(expr* x, expr* y);
    expr_ref if_eq(expr* n, unsigned k, expr* th, expr* el);
    expr* amod(expr* bv_expr, expr* x, rational const& N);
    rational bv_size(expr* bv_expr);
    expr_ref mk_le(expr* a, expr* b);
    expr_ref mk_lt(expr* a, expr* b);
    expr_ref mk_ge(expr* a, expr* b) { return mk_le(b, a); }
    expr_ref mk_gt(expr* a, expr* b) { return mk_lt(b, a); }
    
    
    void translate_bv(app* e);
    void translate_basic(app* e);
    void translate_app(app* e);
    void translate_quantifier(quantifier* q);
    void translate_var(var* v);
    

public:
    bv2int_translator(ast_manager& m, bv2int_translator_trail& ctx);

    void ensure_translated(expr* e);

    void translate_eq(expr* e);

    bool is_translated(expr* e) const { return !!m_translate.get(e->get_id(), nullptr); }
    expr* translated(expr* e) const { expr* r = m_translate.get(e->get_id(), nullptr); SASSERT(r); return r; }

    void internalize_bv(app* e);
    void translate_expr(expr* e);

    expr_ref_vector const& vars() const { return m_vars; }
    expr_ref_vector const& preds() const { return m_preds; }
    ptr_vector<app> const& bv2int() const { return m_bv2int; }
    ptr_vector<app> const& int2bv() const { return m_int2bv; }

    void reset(bool is_plugin);
       
};
