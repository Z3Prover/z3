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

#include "ast/rewriter/bit_blaster/bit_blaster.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"

void mk_bits(ast_manager & m, char const * prefix, unsigned sz, expr_ref_vector & r) {
    sort_ref b(m);
    b = m.mk_bool_sort();
    for (unsigned i = 0; i < sz; ++i) {
        char buffer[128];
#ifdef _WINDOWS
        sprintf_s(buffer, ARRAYSIZE(buffer), "%s%d.smt", prefix, i);
#else
        sprintf(buffer, "%s%d.smt", prefix, i);
#endif
        r.push_back(m.mk_const(symbol(buffer), b));
    }
}

void display(std::ostream & out, expr_ref_vector & r, bool ll=true) {
    ast_mark v;
    for (unsigned i = 0; i < r.size(); i++) {
        if (ll)
            ast_ll_pp(out, r.get_manager(), r.get(i), v);
        else
            out << mk_pp(r.get(i), r.get_manager());
        out << "\n";
    }
}

void tst_adder(ast_manager & m, unsigned sz) {
//     expr_ref_vector a(m);
//     expr_ref_vector b(m);
//     expr_ref_vector c(m);
//     mk_bits(m, "a", sz, a);
//     mk_bits(m, "b", sz, b);
//     bool t = true;
//     bit_blaster blaster(m, t);
//     blaster.mk_adder(sz, a.c_ptr(), b.c_ptr(), c);
//     TRACE("bit_blaster", display(tout, c););
}

void tst_multiplier(ast_manager & m, unsigned sz) {
//     expr_ref_vector a(m);
//     expr_ref_vector b(m);
//     expr_ref_vector c(m);
//     mk_bits(m, "a", sz, a);
//     mk_bits(m, "b", sz, b);
//     bool t = true;
//     bit_blaster blaster(m, t);
//     blaster.mk_multiplier(sz, a.c_ptr(), b.c_ptr(), c);
//     TRACE("bit_blaster", display(tout, c););
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
    tst_adder(m, 4);
    tst_multiplier(m, 4);
    tst_le(m, 4);
    tst_eqs(m, 8);
    tst_sh(m, 4);
}
