/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    char_rewriter.cpp

Abstract:

    Basic rewriting rules for character constraints

Author:

    Nikolaj Bjorner (nbjorner) 2015-12-5

--*/

#include "util/debug.h"
#include "ast/rewriter/char_rewriter.h"
#include "ast/bv_decl_plugin.h"
#include "ast/arith_decl_plugin.h"


char_rewriter::char_rewriter(ast_manager& m):
    m(m) {
    m_char = static_cast<char_decl_plugin*>(m.get_plugin(m.mk_family_id("char")));
}

family_id char_rewriter::get_fid() {
    return m_char->get_family_id();
}

br_status char_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(f->get_family_id() == get_fid());
    br_status st = BR_FAILED;
    switch (f->get_decl_kind()) {
    case OP_CHAR_CONST:
        break;
    case OP_CHAR_LE:
        st = mk_char_le(args[0], args[1], result);
        break;
    case OP_CHAR_TO_INT:
        st = mk_char_to_int(args[0], result);        
        break;
    case OP_CHAR_TO_BV:
        st = mk_char_to_bv(args[0], result);
        break;
    case OP_CHAR_FROM_BV:
        st = mk_char_from_bv(args[0], result);
        break;
    case OP_CHAR_IS_DIGIT:
        st = mk_char_is_digit(args[0], result);
        break;
    }
    return st;
}

br_status char_rewriter::mk_char_is_digit(expr* a, expr_ref& result) {
    unsigned n;
    if (!m_char->is_const_char(a, n))
        return BR_FAILED;
    result = m.mk_bool_val('0' <= n && n <= '9');
    return BR_DONE;
}

br_status char_rewriter::mk_char_to_bv(expr* a, expr_ref& result) {
    return BR_FAILED;
}

br_status char_rewriter::mk_char_le(expr* a, expr* b, expr_ref& result) {
    unsigned na = 0, nb = 0;
    if (m_char->is_const_char(a, na)) {
        if (na == 0) {
            result = m.mk_true();
            return BR_DONE;
        }
    }
    if (m_char->is_const_char(b, nb)) {
        if (na != 0) {
            result = m.mk_bool_val(na <= nb);
            return BR_DONE;
        }
        if (nb == m_char->max_char()) {
            result = m.mk_true();
            return BR_DONE;
        }
    }
    return BR_FAILED;
}

br_status char_rewriter::mk_char_from_bv(expr* e, expr_ref& result) {
    bv_util bv(m);
    rational n;
    if (bv.is_numeral(e, n) && n.is_unsigned() && n <= m_char->max_char()) {
        result = m_char->mk_char(n.get_unsigned());
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status char_rewriter::mk_char_to_int(expr* e, expr_ref& result) {
    unsigned n = 0;
    if (m_char->is_const_char(e, n)) {
        arith_util arith(m);
        result = arith.mk_int(n);
        return BR_DONE;
    }
    return BR_FAILED;
}
