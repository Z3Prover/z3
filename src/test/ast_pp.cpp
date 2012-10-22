/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    tst_ast_pp.cpp

Abstract:

    Test AST Pretty printing module

Author:

    Nikolaj Bjorner (nbjorner) 2006-10-5

Revision History:

--*/
#include "ast.h"
#include "ast_pp.h"
#include "ast_dag_pp.h"
#include "smtparser.h"
#include <iostream>

void tst_ast_pp()
{
    ast_manager m;
    smtlib::parser* parser = smtlib::parser::create(m);

    parser->initialize_smtlib();


    if (!parser->parse_string(
            "(benchmark test :extrasorts (A B) :extrafuns ((f A A) (g A A A) (x A) (p A bool)) \n"
            ":formula (p (f x))\n"
            ":extrafuns ((x1 Int) (y1 Int))\n"
            ":formula (<= 1 (+ x1 y1))\n"
            ":formula (let (x (g x x)) (let (x (g x x)) (let (x (g x x)) (let (x (g x x)) (p (g x x))))))\n"
            ":formula (p x)\n"
            ")")) {
        SASSERT(false);
        dealloc(parser);
        return;
    }

    smtlib::benchmark* b = parser->get_benchmark();

    for (unsigned j = 0; j < b->get_num_assumptions(); ++j) {
		expr* e = b->get_assumptions()[j];
        std::cout << mk_pp(e, m) << "\n";
        ast_dag_pp(std::cout, m, e);
    }
    for (unsigned j = 0; j < b->get_num_formulas(); ++j) {
		expr* e = b->begin_formulas()[j];
        std::cout << mk_pp(e, m) << "\n";
        ast_dag_pp(std::cout, m, e);
    }
    dealloc(parser);
}
