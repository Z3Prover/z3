/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    bit_blaster.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-05.

Revision History:

--*/

#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/bit_blaster/bit_blaster.h"
#include "model/model.h"
#include "model/model_evaluator.h"

void mk_bits(ast_manager & m, char const * prefix, unsigned sz, expr_ref_vector & r) {
    sort_ref b(m);
    b = m.mk_bool_sort();
    for (unsigned i = 0; i < sz; ++i) {
        std::stringstream ous;
        ous << prefix << i << ".smt2";
        r.push_back(m.mk_const(symbol(ous.str()), b));
    }
}

void display(std::ostream & out, expr_ref_vector & r, bool ll=true) {
    for (unsigned i = 0; i < r.size(); i++) {
        out << "bit " << i << ":\n";
        if (ll)
            ast_ll_pp(out, r.get_manager(), r.get(i));
        else
            out << mk_pp(r.get(i), r.get_manager()) << "\n";
    }
}

static unsigned to_int(model_core & mdl, expr_ref_vector & out) {
    SASSERT(out.size() <= sizeof(unsigned) * 8);
    ast_manager & m = mdl.get_manager();
    model_evaluator eval(mdl);
    expr_ref bit(m);
    unsigned actual = 0;
    for (unsigned i = 0; i < out.size(); i++) {
        eval(out.get(i), bit);
        if (m.is_true(bit))
            actual |= 1 << i;
        else
            ENSURE(m.is_false(bit));
    }
    return actual;
}

#define ENSURE_INT(mdl, out, expected) \
    do { \
        unsigned actual = to_int(mdl, out); \
        TRACE("bit_blaster", \
            display(tout, out); \
            tout << "expected=" << (expected) << ", actual=" << actual << "\n"; \
        ); \
        ENSURE(actual == (expected)); \
    } while (0)

void tst_adder(ast_manager & m, bit_blaster & blaster) {
    model mdl(m);
    expr_ref_vector c(m);
    app_ref b1(m.mk_const("b1", m.mk_bool_sort()), m);
    app_ref b2(m.mk_const("b2", m.mk_bool_sort()), m);
    expr_ref not_b1(m.mk_not(b1), m);

    {
        expr * const a[] = { b1, b1, b1 };
        expr * const b[] = { m.mk_false(), m.mk_true(), m.mk_true() };
        c.reset();
        blaster.mk_adder(3, a, b, c);
    }

    mdl.register_decl(b1->get_decl(), m.mk_false());
    ENSURE_INT(mdl, c, 6); // b000 + b110

    mdl.register_decl(b1->get_decl(), m.mk_true());
    ENSURE_INT(mdl, c, 5); // b111 + b110

    {
        expr * const a[] = { m.mk_false(), m.mk_true(), m.mk_true() };
        expr * const b[] = { b1, not_b1, m.mk_false() };
        c.reset();
        blaster.mk_adder(3, a, b, c);
    }

    mdl.register_decl(b1->get_decl(), m.mk_false());
    ENSURE_INT(mdl, c, 0); // b110 + b010

    mdl.register_decl(b1->get_decl(), m.mk_true());
    ENSURE_INT(mdl, c, 7); // b110 + b001

    {
        expr * const a[] = { b1, b2, m.mk_true() };
        expr * const b[] = { b1, not_b1, m.mk_false() };
        c.reset();
        blaster.mk_adder(3, a, b, c);
    }

    mdl.register_decl(b1->get_decl(), m.mk_false());
    mdl.register_decl(b2->get_decl(), m.mk_false());
    ENSURE_INT(mdl, c, 6); // b100 + b010

    mdl.register_decl(b1->get_decl(), m.mk_false());
    mdl.register_decl(b2->get_decl(), m.mk_true());
    ENSURE_INT(mdl, c, 0); // b110 + b010

    mdl.register_decl(b1->get_decl(), m.mk_true());
    mdl.register_decl(b2->get_decl(), m.mk_false());
    ENSURE_INT(mdl, c, 6); // b101 + b001

    mdl.register_decl(b1->get_decl(), m.mk_true());
    mdl.register_decl(b2->get_decl(), m.mk_true());
    ENSURE_INT(mdl, c, 0); // b111 + b001
}

void tst_multiplier(ast_manager & m, bit_blaster & blaster) {
    model mdl(m);
    expr_ref_vector c(m);
    app_ref b1(m.mk_const("b1", m.mk_bool_sort()), m);
    app_ref b2(m.mk_const("b2", m.mk_bool_sort()), m);
    expr_ref not_b1(m.mk_not(b1), m);

    {
        expr * const a[] = { b1, b1, b1 };
        expr * const b[] = { m.mk_false(), m.mk_true(), m.mk_true() };
        c.reset();
        blaster.mk_multiplier(3, a, b, c);
    }

    mdl.register_decl(b1->get_decl(), m.mk_false());
    ENSURE_INT(mdl, c, 0); // b000 * b110

    mdl.register_decl(b1->get_decl(), m.mk_true());
    ENSURE_INT(mdl, c, 2); // b111 * b110

    {
        expr * const a[] = { m.mk_false(), m.mk_true(), m.mk_true() };
        expr * const b[] = { b1, not_b1, m.mk_false() };
        c.reset();
        blaster.mk_multiplier(3, a, b, c);
    }

    mdl.register_decl(b1->get_decl(), m.mk_false());
    ENSURE_INT(mdl, c, 4); // b110 * b010

    mdl.register_decl(b1->get_decl(), m.mk_true());
    ENSURE_INT(mdl, c, 6); // b110 * b001

    {
        expr * const a[] = { b1, b2, m.mk_true() };
        expr * const b[] = { b1, not_b1, m.mk_false() };
        c.reset();
        blaster.mk_multiplier(3, a, b, c);
    }

    mdl.register_decl(b1->get_decl(), m.mk_false());
    mdl.register_decl(b2->get_decl(), m.mk_false());
    ENSURE_INT(mdl, c, 0); // b100 * b010

    mdl.register_decl(b1->get_decl(), m.mk_false());
    mdl.register_decl(b2->get_decl(), m.mk_true());
    ENSURE_INT(mdl, c, 4); // b110 * b010

    mdl.register_decl(b1->get_decl(), m.mk_true());
    mdl.register_decl(b2->get_decl(), m.mk_false());
    ENSURE_INT(mdl, c, 5); // b101 * b001

    mdl.register_decl(b1->get_decl(), m.mk_true());
    mdl.register_decl(b2->get_decl(), m.mk_true());
    ENSURE_INT(mdl, c, 7); // b111 * b001
}

void tst_le(ast_manager & m, unsigned sz) {
//     expr_ref_vector a(m);
//     expr_ref_vector b(m);
//     expr_ref out(m);
//     mk_bits(m, "a", sz, a);
//     mk_bits(m, "b", sz, b);
//     bool t = true;
//     bit_blaster blaster(m, t);
//     blaster.mk_ule(sz, a.c_ptr(), b.c_ptr(), out); 
//     TRACE("bit_blaster", tout << mk_pp(out, m) << "\n";);
//     blaster.mk_sle(sz, a.c_ptr(), b.c_ptr(), out);
//     TRACE("bit_blaster", tout << mk_pp(out, m) << "\n";);
}

void tst_eqs(ast_manager & m, unsigned sz) {
//     expr_ref_vector a(m);
//     expr_ref_vector b(m);
//     expr_ref out(m);
//     mk_bits(m, "a", sz, a);
//     bool t = true;
//     bit_blaster blaster(m, t);
//     blaster.mk_eqs(sz, a.c_ptr(), b); 
//     TRACE("bit_blaster", display(tout, b, false););
}

void tst_sh(ast_manager & m, unsigned sz) {
//     expr_ref_vector a(m);
//     expr_ref_vector b(m);
//     expr_ref_vector c(m);
//     mk_bits(m, "a", sz, a);
//     mk_bits(m, "b", sz, b);
//     bool t = true;
//     bit_blaster blaster(m, t);
//     blaster.mk_shl(sz, a.c_ptr(), b.c_ptr(), c);
//     TRACE("bit_blaster", tout << "shl\n"; display(tout, c););
//     c.reset();
//     blaster.mk_lshr(sz, a.c_ptr(), b.c_ptr(), c);
//     TRACE("bit_blaster", tout << "lshr\n"; display(tout, c););
//     c.reset();
//     blaster.mk_ashr(sz, a.c_ptr(), b.c_ptr(), c);
//     TRACE("bit_blaster", tout << "ashr " << c.size() << "\n"; display(tout, c, false););
}

void tst_bit_blaster() {
    ast_manager m;
    reg_decl_plugins(m);
    bit_blaster_params params;
    bit_blaster blaster(m, params);

    tst_adder(m, blaster);
    tst_multiplier(m, blaster);
    tst_le(m, 4);
    tst_eqs(m, 8);
    tst_sh(m, 4);
}
