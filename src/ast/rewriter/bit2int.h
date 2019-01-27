/*++
Copyright (c) 2009 Microsoft Corporation

Module Name:

    bit2int.h

Abstract:

    Routines for simplifying bit2int expressions.

Author:

    Nikolaj Bjorner (nbjorner) 2009-08-28

Revision History:

--*/
#ifndef BIT2INT_H_
#define BIT2INT_H_

#include "ast/bv_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/act_cache.h"
#include "ast/rewriter/bv_rewriter.h"

class bit2int {
protected:
    typedef rational numeral;

    enum eq_type {
        lt, 
        le,
        eq
    };

    class expr_reduce {
        bit2int& m_super;
    public:
        expr_reduce(bit2int& s) : m_super(s) {}
        
        void operator()(var* v) {
            m_super.cache_result(v, v);
        }

        void operator()(quantifier* q) {
            m_super.visit(q);
        }
        
        void operator()(app* a) {
            m_super.visit(a);
        }

        void operator()(ast* a) {}

    };

    typedef act_cache expr_map;
    ast_manager &             m_manager;
    bv_util                   m_bv_util;
    bv_rewriter               m_rewriter;
    arith_util                m_arith_util;

    expr_map                  m_cache;      // map: ast  -> ast    ref. counters are incremented when inserted here.
    expr_ref                  m_bit0;
    ptr_vector<expr>  m_args;        


    void visit(app* n);
    void visit(quantifier* q);
    unsigned get_b2i_size(expr * n);
    bool extract_bv(expr* n, unsigned& sz, bool& sign, expr_ref& bv);
    unsigned get_numeral_bits(numeral const& k);
    bool is_bv_poly(expr* n, expr_ref& pos, expr_ref& neg);
    bool mk_mul(expr* a, expr* b, expr_ref& result);
    bool mk_comp(eq_type ty, expr* e1, expr* e2, expr_ref& result);
    bool mk_add(expr* e1, expr* e2, expr_ref& result);

    expr * get_cached(expr * n) const;
    bool is_cached(expr * n) const {  return get_cached(n) != nullptr; }
    void cache_result(expr * n, expr * r);
    void reset_cache() { m_cache.reset(); }
    void flush_cache() { m_cache.cleanup(); }
    void align_size(expr* e, unsigned sz, expr_ref& result);
    void align_sizes(expr_ref& a, expr_ref& b);

public:
    bit2int(ast_manager & m);
    void operator()(expr * m, expr_ref & result, proof_ref& p);
};

#endif /* BIT2INT_H_ */

