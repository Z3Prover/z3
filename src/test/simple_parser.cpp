/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    simple_parser.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-14.

Revision History:

--*/
#include "parsers/util/cost_parser.h"
#include "smt/cost_evaluator.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/well_sorted.h"
#include "util/warning.h"
#include "ast/reg_decl_plugins.h"

void tst_simple_parser() {
    ast_manager    m;
    reg_decl_plugins(m);
    arith_util     m_util(m);
    cost_parser    p(m);
    var_ref_vector vs(m);
    cost_evaluator eval(m);
    p.add_var("x");
    p.add_var("y");
    expr_ref r(m);
    p.parse_string("(+ x (* y x))", r);
    TRACE("simple_parser", tout << mk_pp(r, m) << "\n";);
    p.parse_string("(+ x (* y x) x)", r);
    float vals[2] = { 2.0f, 3.0f };
    (void)vals;
    TRACE("simple_parser",
          tout << mk_pp(r, m) << "\n";
          tout << "val: " << eval(r, 2, vals) << "\n";);
    p.parse_string("(+ x (* y x) x", r); // << error
    p.parse_string("(x)", r); // << error
    p.parse_string("(+ x))", r); // <<< this is accepted
    TRACE("simple_parser", tout << mk_pp(r, m) << "\n";);
    p.parse_string(")x)", r); // error
    p.parse_string("(+ x (* 10 y) 2)", r);
    TRACE("simple_parser", 
          tout << mk_pp(r, m) << "\n";
          tout << "val: " << eval(r, 2, vals) << "\n";);
    p.parse_string("(ite (and (> x 3) (<= y 4))  2 10)", r);
    TRACE("simple_parser", 
          tout << mk_pp(r, m) << "\n";
          tout << "val: " << eval(r, 2, vals) << "\n";);
    p.parse_string("(ite (or (> x 3) (<= y 4))  2 10)", r);
    TRACE("simple_parser", 
          tout << mk_pp(r, m) << "\n";
          tout << "val: " << eval(r, 2, vals) << "\n";);
}

