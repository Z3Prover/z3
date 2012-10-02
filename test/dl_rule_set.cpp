/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_rule_set.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-05-18.

Revision History:

--*/
#include"dl_context.h"
#include"dl_rule_set.h"
#include"dl_mk_filter_rules.h"
#include"dl_mk_simple_joins.h"
#include"smtparser.h"
#include"ast_pp.h"
#include<iostream>
#include<sstream>

void tst_dl_rule_set() {
    enable_trace("mk_filter_rules");
    front_end_params params;
    ast_manager m;
    smtlib::parser * parser = smtlib::parser::create(m);
    parser->initialize_smtlib();
    datalog::context ctx(m, params);
    datalog::rule_set rs(ctx);
    datalog::rule_manager& rm = ctx.get_rule_manager();
    datalog::rule_ref_vector rv(rm);


    if (!parser->parse_string(
            "(benchmark test\n"
            ":extrapreds ((T Int Int) (Q Int Int) (R Int Int Int) (S Int Int Int) (DynActual Int Int Int) (GlobalSym Int Int) (HeapPointsTo Int Int Int) (Calls Int Int)) \n"
            ":extrapreds ((Actual Int Int Int) (PointsTo Int Int) (PointsTo0 Int Int) (FuncDecl0 Int Int) (Assign Int Int) (Load Int Int Int))\n"
            ":formula (forall (x Int) (=> (Q x 1) (T x x)))\n"
            ":formula (forall (v Int) (h Int) (=> (PointsTo0 v h) (PointsTo v h)))\n"
            ":formula (forall (v Int) (h Int) (=> (FuncDecl0 v h) (PointsTo v h)))\n"
            ":formula (forall (v Int) (h Int) (=> (FuncDecl0 v h) (PointsTo v h)))\n"
            ":formula (forall (v1 Int) (v2 Int) (h Int) (=> (and (PointsTo v2 h) (Assign v1 v2)) (PointsTo v1 h)))\n"
            ":formula (forall (x Int) (y Int) (z Int) (=> (and (Q x y) (T y z)) (T x y)))\n"
            ":formula (forall (i1 Int) (v Int) (fun Int) (c Int) (v1 Int) (h Int) (h1 Int) (=> (and (GlobalSym 0 fun) (HeapPointsTo fun 1 c) (Calls i1 c) (Actual i1 3 v1) (PointsTo v1 h) (HeapPointsTo h 0 h1) (PointsTo v h1)) (DynActual i1 2 v)))\n"
            ":formula (forall (i1 Int) (v Int) (fun Int) (c Int) (v1 Int) (h Int) (h1 Int) (=> (and (GlobalSym 0 fun) (HeapPointsTo fun 1 c) (Calls i1 c) (Actual i1 3 v1) (PointsTo v1 h) (HeapPointsTo h 1 h1) (PointsTo v h1)) (DynActual i1 3 v)))\n"
            ":formula (forall (i1 Int) (v Int) (fun Int) (c Int) (v1 Int) (h Int) (h1 Int) (=>  (and (GlobalSym 0 fun) (HeapPointsTo fun 1 c) (Calls i1 c) (Actual i1 3 v1) (PointsTo v1 h) (HeapPointsTo h 2 h1) (PointsTo v h1)) (DynActual i1 4 v)))\n"
            ":formula (forall (v1 Int) (v2 Int) (h1 Int) (h2 Int) (f Int) (=> (and (Load v2 v1 f) (PointsTo v1 h1) (HeapPointsTo h1 f h2)) (PointsTo v2 h1)))\n"
            ":formula (forall (v1 Int) (v2 Int) (h1 Int) (h2 Int) (f Int) (=> (and (Load v2 v1 0) (HeapPointsTo h1 f h2)) (PointsTo v2 h1)))\n"
            ":formula (forall (v1 Int) (v2 Int) (h1 Int) (h2 Int) (f Int) (=> (and  (not (Load v2 v1 0)) (HeapPointsTo h1 f h2)) (PointsTo v2 h1)))\n"
            ")")) {
        SASSERT(false);
        dealloc(parser);
        return;
    }

    smtlib::benchmark * b = parser->get_benchmark();


    for (unsigned j = 0; j < b->get_num_formulas(); ++j) {
        expr * e = b->begin_formulas()[j];
        ptr_vector<expr> todo;
        todo.push_back(e);
        while (!todo.empty()) {
            e = todo.back();
            todo.pop_back();
            if (is_quantifier(e)) {
                e = to_quantifier(e)->get_expr();
                todo.push_back(e);
            }
            else if (is_app(e)) {
                app* a = to_app(e);
                if (is_uninterp(e) && !ctx.is_predicate(a->get_decl())) {
                    std::cout << "registering " << a->get_decl()->get_name() << "\n";
                    
                    ctx.register_predicate(a->get_decl());
                }
                else {
                    todo.append(a->get_num_args(), a->get_args());
                }
            }
        }
    }
    

    for (unsigned j = 0; j < b->get_num_formulas(); ++j) {
        expr * e = b->begin_formulas()[j];
        if (is_quantifier(e)) {
            try {
                rm.mk_rule(e, rv);
            }
            catch(...) {
                std::cerr << "ERROR: it is not a valid Datalog rule:\n" << mk_pp(e, m) << "\n";
            }
        }
    }
    rs.add_rules(rv.size(), rv.c_ptr());
    rs.display(std::cout);

    datalog::mk_filter_rules p(ctx);
    model_converter_ref mc;
    proof_converter_ref pc;
    datalog::rule_set * new_rs = p(rs, mc, pc);
    std::cout << "\nAfter mk_filter:\n";
    new_rs->display(std::cout);
    datalog::mk_simple_joins p2(ctx);
    datalog::rule_set * new_rs2 = p2(*new_rs, mc, pc);
    std::cout << "\nAfter mk_simple_joins:\n";
    new_rs2->display(std::cout);
    dealloc(new_rs);
    dealloc(new_rs2);
    dealloc(parser);
}
