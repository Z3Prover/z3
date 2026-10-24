/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    ff_bv_operations.h

Abstract:

    Canonical field arithmetic shared by eager translation (ff2bv) and the
    lazy SMT bridge (theory_ff). Each caller owns its own traversal, range
    bounds, and model conversion.

Author:

    Romain Soulat

--*/
#pragma once
#include "ast/ff_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"

// Canonical field arithmetic shared by eager translation and the lazy SMT
// bridge. Each caller owns its traversal, range bounds and model conversion.
class ff_bv_operations {
    ast_manager &m;
    ff_util ff;
    bv_util bv;
    th_rewriter &rw;
public:
    ff_bv_operations(ast_manager &m, th_rewriter &rw): m(m), ff(m), bv(m), rw(rw) {}
    expr_ref reduce(expr *x, sort *field, unsigned wide) {
        // Unsigned remainder chooses the canonical residue in [0,p-1].
        // It fits in w bits, so extracting the low w bits loses no value.
        unsigned w = ff.width(field);
        expr_ref p(bv.mk_numeral(ff.modulus(field), wide), m);
        expr_ref r(bv.mk_bv_urem(x, p), m);
        if (wide != w)
            r = bv.mk_extract(w - 1, 0, r);
        rw(r);
        return r;
    }
    expr_ref binary(expr *a, expr *b, sort *field, bool mul) {
        // Canonical inputs satisfy 0<=a,b<p<=2^w. Their sum fits in
        // w+1 bits and product in 2*w bits, so widening BEFORE arithmetic
        // prevents BV overflow from changing the subsequent reduction mod p.
        unsigned w = ff.width(field), wide = mul ? 2 * w : w + 1;
        expr_ref x(bv.mk_zero_extend(wide - w, a), m), y(bv.mk_zero_extend(wide - w, b), m);
        expr_ref r(mul ? bv.mk_bv_mul(x, y) : bv.mk_bv_add(x, y), m);
        return reduce(r, field, wide);
    }
    expr_ref apply(app *a, expr_ref_vector const &args) {
        sort *s = a->get_sort();
        rational value;
        if (ff.is_numeral(a, value)) return expr_ref(bv.mk_numeral(value, ff.width(s)), m);
        expr_ref r(m);
        if (ff.is_neg(a)) {
            // Canonical x satisfies 0 <= p-x <= p; remainder maps -0 to 0.
            unsigned w = ff.width(s);
            expr_ref x(bv.mk_zero_extend(1, args.get(0)), m);
            r = bv.mk_bv_sub(bv.mk_numeral(ff.modulus(s), w + 1), x);
            return reduce(r, s, w + 1);
        }
        if (ff.is_add(a) || ff.is_mul(a)) {
            r = args.get(0);
            for (unsigned i = 1; i < args.size(); ++i)
                r = binary(r, args.get(i), s, ff.is_mul(a));
            return r;
        }
        if (ff.is_bitsum(a)) {
            // Horner's identity holds modulo p without Boolean/no-wrap assumptions.
            r = args.back();
            for (unsigned i = args.size() - 1; i-- > 0;) {
                r = binary(r, r, s, false);
                r = binary(r, args.get(i), s, false);
            }
            return r;
        }
        UNREACHABLE();
        return r;
    }
};
