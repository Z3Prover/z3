/*++
Copyright (c) 2008 Microsoft Corporation

Module Name:

    tst_ast_smt_pp.cpp

Abstract:

    Test AST Pretty printing module

Author:

    Nikolaj Bjorner (nbjorner) 2008-09-04

Revision History:

--*/
#include "ast.h"
#include "ast_smt_pp.h"
#include "smtparser.h"
#include <iostream>
#include <sstream>

void tst_ast_smt_pp()
{
    ast_manager m;
    smtlib::parser* parser = smtlib::parser::create(m);

    parser->initialize_smtlib();


    if (!parser->parse_string(
            "(benchmark test :extrasorts (A B) :extrafuns ((f A A) (g A A A) (x A) (p A bool)) \n"
            ":extrafuns ((arg0 BitVec[8]) (arg1 BitVec[8]) (arg2 BitVec[8]))\n"
            ":formula (p (f x))\n"
            ":extrafuns ((x1 Int) (y1 Int))\n"
            ":formula (<= 1 (+ x1 y1))\n"
            ":formula (let (x (g x x)) (let (x (g x x)) (let (x (g x x)) (let (x (g x x)) (p (g x x))))))\n"
            ":formula (p x)\n"
            ":formula (bvsge (bvadd arg0 arg2) (extract[7:0] bv3[32]))\n"
            ":formula (forall (x Int) (y Int) (z Int) (and (<= 1 x) (<= x y)))   \n"
            ":formula (forall (x Int) (y Int) (z Int) (and (<= 2 (ite (<= z 1) x (* 2 x))) (<= x y)))\n"
            ":formula (forall (x Int) (y Int) (and (<= 2 (ite (forall (z Int) (<= z 1)) x (* 2 x))) (<= x y)))\n"
            ":formula (forall (x Int) (y Int) (and (<= 2 (ite (forall (z Int) (or (> x y) (<= z 1))) x (* 2 x))) (<= x y)))\n"
            ":extrafuns ((a1 Array))\n"
            ":formula (= x1 (select (store a1 y1 y1) x1))\n"
            ":extrafuns ((a2 Array[32:8]))\n"
            ":formula (= arg0 (select a2 bv0[32]))\n"
            ":datatypes ((list (cons (car Int) (cdr list)) nil))\n"
            ":extrafuns ((a list) (b list) (c list))\n"
            ":formula (is_nil nil)\n"
            ":datatypes ((list1 (cons1 (car1 Int) (cdr1 list2)) nil1) (list2 (cons1 (car2 list) (cdr2 list1)) nil2) )\n"
            ":formula (is_nil2 nil2)\n"
            ")")) {
        SASSERT(false);
        dealloc(parser);
        return;
    }

    smtlib::benchmark* b = parser->get_benchmark();

    for (unsigned j = 0; j < b->get_num_formulas(); ++j) {
        expr* e = b->begin_formulas()[j];
        ast_smt_pp pp(m);
        pp.display(std::cout, e);
    }


    for (unsigned j = 0; j < b->get_num_formulas(); ++j) {
        expr* e = b->begin_formulas()[j];

        // print and parse formula again.
        std::ostringstream buffer;        
        ast_smt_pp pp(m);
        pp.display(buffer, e);
        ast_manager m2;
        smtlib::parser* parser2 = smtlib::parser::create(m2);
        parser2->initialize_smtlib();
        if (!parser2->parse_string(buffer.str().c_str())) {
            SASSERT(false);
            dealloc(parser2);
            return;
        }
        dealloc(parser2);
    }


    dealloc(parser);
}
