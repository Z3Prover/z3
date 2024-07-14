/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    bv_sls_terms.cpp

Abstract:

    normalize bit-vector expressions to use only binary operators.

Author:

    Nikolaj Bjorner (nbjorner) 2024-02-07
    
--*/

#include "ast/ast_ll_pp.h"
#include "ast/sls/bv_sls_terms.h"
#include "ast/rewriter/bool_rewriter.h"
#include "ast/rewriter/bv_rewriter.h"

namespace bv {

    sls_terms::sls_terms(sls::context& ctx):
        ctx(ctx),
        m(ctx.get_manager()), 
        bv(m),
        m_axioms(m) {}

    void sls_terms::register_term(expr* e) {
        auto r = ensure_binary(e);
        if (r != e)
            m_axioms.push_back(m.mk_eq(e, r));
    }

    expr_ref sls_terms::ensure_binary(expr* e) {

        app* a = to_app(e);
        auto arg = [&](unsigned i) {
            return a->get_arg(i);
        };
        unsigned num_args = a->get_num_args();
        expr_ref r(m);
#define FOLD_OP(oper)           \
        r = arg(0);             \
        for (unsigned i = 1; i < num_args; ++i)\
            r = oper(r, arg(i)); \

        if (bv.is_concat(e)) {
            FOLD_OP(bv.mk_concat);
        }
        else if (bv.is_bv_sdiv(e) || bv.is_bv_sdiv0(e) || bv.is_bv_sdivi(e)) {
            r = mk_sdiv(arg(0), arg(1));
        }
        else if (bv.is_bv_smod(e) || bv.is_bv_smod0(e) || bv.is_bv_smodi(e)) {
            r = mk_smod(arg(0), arg(1));
        }
        else if (bv.is_bv_srem(e) || bv.is_bv_srem0(e) || bv.is_bv_sremi(e)) {
            r = mk_srem(arg(0), arg(1));
        }
        else
            r = e;                   
        return r;
    }

    expr_ref sls_terms::mk_sdiv(expr* x, expr* y) {
        // d = udiv(abs(x), abs(y))
        // y = 0, x >= 0 -> -1
        // y = 0, x < 0 -> 1
        // x = 0, y != 0 -> 0
        // x > 0, y < 0 -> -d
        // x < 0, y > 0 -> -d
        // x > 0, y > 0 -> d
        // x < 0, y < 0 -> d
        bool_rewriter br(m);
        bv_rewriter bvr(m);
        unsigned sz = bv.get_bv_size(x);
        rational N = rational::power_of_two(sz);
        expr_ref z(bv.mk_zero(sz), m);
        expr_ref o(bv.mk_one(sz), m);
        expr_ref n1(bv.mk_numeral(N - 1, sz), m);
        expr_ref signx = bvr.mk_ule(bv.mk_numeral(N / 2, sz), x);
        expr_ref signy = bvr.mk_ule(bv.mk_numeral(N / 2, sz), y);
        expr_ref absx = br.mk_ite(signx, bvr.mk_bv_neg(x), x);
        expr_ref absy = br.mk_ite(signy, bvr.mk_bv_neg(y), y);
        expr_ref d = expr_ref(bv.mk_bv_udiv(absx, absy), m);
        expr_ref r = br.mk_ite(br.mk_eq(signx, signy), d, bvr.mk_bv_neg(d));
        r = br.mk_ite(br.mk_eq(z, y),
                br.mk_ite(signx, o, n1),
                     br.mk_ite(br.mk_eq(x, z), z, r));
        return r;
    }

    expr_ref sls_terms::mk_smod(expr* x, expr* y) {
        // u := umod(abs(x), abs(y))
        // u = 0 ->  0
        // y = 0 ->  x
        // x < 0, y < 0 ->  -u
        // x < 0, y >= 0 ->  y - u
        // x >= 0, y < 0 ->  y + u
        // x >= 0, y >= 0 ->  u
        bool_rewriter br(m);
        bv_rewriter bvr(m);
        unsigned sz = bv.get_bv_size(x);
        expr_ref z(bv.mk_zero(sz), m);
        expr_ref abs_x = br.mk_ite(bvr.mk_sle(z, x), x, bvr.mk_bv_neg(x));
        expr_ref abs_y = br.mk_ite(bvr.mk_sle(z, y), y, bvr.mk_bv_neg(y));
        expr_ref u = bvr.mk_bv_urem(abs_x, abs_y);
        expr_ref r(m);
        r = br.mk_ite(br.mk_eq(u, z), z,
                br.mk_ite(br.mk_eq(y, z), x,
                    br.mk_ite(br.mk_and(bvr.mk_sle(z, x), bvr.mk_sle(z, x)), u,
                        br.mk_ite(bvr.mk_sle(z, x), bvr.mk_bv_add(y, u),
                            br.mk_ite(bv.mk_sle(z, y), bvr.mk_bv_sub(y, u), bvr.mk_bv_neg(u))))));
        return r;
    }

    expr_ref sls_terms::mk_srem(expr* x, expr* y) {
        // y = 0 -> x
        // else x - sdiv(x, y) * y
        expr_ref r(m);
        bool_rewriter br(m);
        bv_rewriter bvr(m);
        expr_ref z(bv.mk_zero(bv.get_bv_size(x)), m);
        r = br.mk_ite(br.mk_eq(y, z), x, bvr.mk_bv_sub(x, bvr.mk_bv_mul(y, mk_sdiv(x, y))));
        return r;
    }

}
