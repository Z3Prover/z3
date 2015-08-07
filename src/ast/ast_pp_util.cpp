/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    ast_pp_util.cpp

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2015-8-6.

Revision History:

--*/

#include "ast_pp_util.h"

void ast_pp_util::collect(expr* e) {
    coll.visit(e);
}

void ast_pp_util::collect(unsigned n, expr* const* es) {
    for (unsigned i = 0; i < n; ++i) {
        coll.visit(es[i]);
    }
}

void ast_pp_util::collect(expr_ref_vector const& es) {
    collect(es.size(), es.c_ptr());
}

void ast_pp_util::display_decls(std::ostream& out) {
    smt2_pp_environment_dbg env(m);
    ast_smt_pp pp(m);
    unsigned n = coll.get_num_sorts();
    for (unsigned i = 0; i < n; ++i) {
        pp.display_ast_smt2(out, coll.get_sorts()[i], 0, 0, 0);
    }
    n = coll.get_num_decls();
    for (unsigned i = 0; i < n; ++i) {
        ast_smt2_pp(out, coll.get_func_decls()[i], env);
        out << "\n";
    }
}

void ast_pp_util::display_asserts(std::ostream& out, expr_ref_vector const& fmls, bool neat) {
    func_decl_ref asrt(m);
    expr_ref e(m);
    sort* b = m.mk_bool_sort();
    asrt = m.mk_func_decl(symbol("assert"), 1, &b, b);
    if (neat) {
        smt2_pp_environment_dbg env(m);
        for (unsigned i = 0; i < fmls.size(); ++i) {
            e = m.mk_app(asrt, fmls[i]);
            ast_smt2_pp(out, e, env);
            out << "\n";
        }
    }
    else {
        ast_smt_pp ll_smt2_pp(m);
        for (unsigned i = 0; i < fmls.size(); ++i) {
            e = m.mk_app(asrt, fmls[i]);
            ll_smt2_pp.display_expr_smt2(out, e);
            out << "\n";
        }
    }
}
