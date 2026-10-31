
/*++
Copyright (c) 2015 Microsoft Corporation

--*/


#include "ast/ast.h"
#include "params/smt_params.h"
#include "smt/smt_context.h"
#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "model/model_v2_pp.h"
#include "model/datatype_factory.h"
#include "ast/reg_decl_plugins.h"
#include "api/z3.h"
#include "cmd_context/cmd_context.h"
#include "parsers/smt2/smt2parser.h"
#include <iostream>
#include <sstream>
#include <string>

static char const* array_datatypes = R"(
(define-sort InoxSet (T) (Array T Bool))
(declare-datatypes ((Regex 0)) (((ElementSet (cs (InoxSet (_ BitVec 16)))) (Concat (r1 Regex) (r2 Regex)) (ElementMatch (c (_ BitVec 16))) (Union (u1 Regex) (u2 Regex)) (EmptyExpr) (Star (reg Regex)) (EmptyLang))))
(declare-datatypes ((RList 0)) (((RCons (rh Regex) (rt RList)) (RNil))))
(declare-datatypes ((Context 0)) (((Context (exprs RList)))))
(declare-datatypes ((Key 0)) (((Key (k1 Context) (k2 (_ BitVec 16))))))
(declare-datatypes ((Entry 0)) (((Entry (key Key) (value (InoxSet Context))))))
(declare-datatypes ((EList 0)) (((ECons (eh Entry) (et EList)) (ENil))))
)";

static void test_fresh_datatype_values(std::string const& declarations) {
    cmd_context cmd;
    std::istringstream input(declarations);
    ENSURE(parse_smt2_commands(cmd, input));
    ast_manager& m = cmd.m();
    model md(m);
    datatype_factory factory(m, md);
    sort* s = cmd.find_func_decl(symbol("v"))->get_range();
    expr_ref_vector values(m);
    obj_hashtable<expr> seen;
    scoped_rlimit limit(m.limit(), 100000);
    values.push_back(factory.get_some_value(s));
    seen.insert(values.back());
    for (unsigned i = 0; i < 32; ++i) {
        expr_ref value(factory.get_fresh_value(s), m);
        if (!value || m.limit().is_canceled())
            std::cout << "fresh value " << i << " for " << s->get_name()
                      << ", resources: " << m.limit().count() << "\n";
        ENSURE(value && !m.limit().is_canceled());
        ENSURE(!seen.contains(value));
        ENSURE(m.is_value(value));
        seen.insert(value);
        values.push_back(value);
    }
}

static void test_array_datatype_model() {
    for (char const* s : {"EList", "RList", "Context", "Key", "Entry"})
        test_fresh_datatype_values(std::string(array_datatypes) + "(declare-const v " + s + ")");
    test_fresh_datatype_values(std::string(array_datatypes) + R"(
(declare-datatypes ((A 0) (B 0))
 (((ANil) (ACons (ab B))) ((BCons (ba A) (noise Regex)))))
(declare-const v A)
)");

    for (unsigned stores : {1u, 3u}) {
        Z3_config cfg = Z3_mk_config();
        Z3_context ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        std::string spec = std::string("(set-option :produce-unsat-assumptions true)\n") +
            array_datatypes + R"(
(declare-fun p () Bool)
(declare-fun nonEmpty () Bool)
(declare-fun arr () (Array (_ BitVec 32) EList))
(declare-fun rest () (Array (_ BitVec 32) EList))
(declare-fun k () (_ BitVec 32))
(declare-fun v () EList)
(assert (=> nonEmpty (= arr (store rest k v))))
)";
        for (unsigned i = 1; i < stores; ++i) {
            std::string suffix = std::to_string(i);
            spec += "(declare-const arr" + suffix + " (Array (_ BitVec 32) EList))\n";
            spec += "(declare-const guard" + suffix + " Bool)\n";
            spec += "(assert (=> guard" + suffix + " (= arr" + suffix + " (store rest k v))))\n";
        }
        spec += "(check-sat p)\n(get-model)\n"
                "(eval (=> nonEmpty (= arr (store rest k v))))\n";
        std::string response = Z3_eval_smtlib2_string(ctx, spec.c_str());
        ENSURE(response.find("sat\n") == 0);
        ENSURE(response.find("define-fun") != std::string::npos);
        ENSURE(response.find("error") == std::string::npos);
        ENSURE(response.ends_with("true\n"));
        Z3_del_context(ctx);
    }
}

void tst_model_retrieval()
{          
    memory::initialize(0);
    test_array_datatype_model();
    smt_params params;
    params.m_model = true;


    ast_manager m;
    reg_decl_plugins(m);

    family_id array_fid = m.mk_family_id(symbol("array"));
    array_util au(m);
    
    // arr_s and select_fn creation copy-pasted from z3.cpp

    parameter sparams[2]  = { parameter(to_sort(m.mk_bool_sort())), parameter(to_sort(m.mk_bool_sort())) };
    sort_ref arr_s(m.mk_sort(array_fid, ARRAY_SORT, 2, sparams), m);

    sort * domain2[2] = {arr_s, m.mk_bool_sort()};
    func_decl_ref select_fn(
        m.mk_func_decl(array_fid, OP_SELECT, 2, arr_s->get_parameters(), 2, domain2), m);


    app_ref a1(m.mk_const(symbol("a1"), arr_s), m);
    app_ref a2(m.mk_const(symbol("a2"), arr_s), m);

    // (= true (select a1 true))
    app_ref fml(m.mk_eq(m.mk_true(),
        m.mk_app(select_fn.get(), a1, m.mk_true())), m);

    smt::context ctx(m, params);
    ctx.assert_expr(fml);
    lbool check_result = ctx.check();
    std::cout<<((check_result==l_true) ? "satisfiable" : 
                (check_result==l_false) ? "unsatisfiable" : "unknown")<<"\n";
    ref<model> model;
    ctx.get_model(model);
    model_v2_pp(std::cout, *model, false);
    expr_ref a1_val(model->get_const_interp(a1->get_decl()), m);

    app_ref fml2(m.mk_eq(a2, a1_val), m);
    ctx.assert_expr(fml2);
    std::cout<<"--------------------------\n";
    ctx.display(std::cout);
    std::cout<<"--------------------------\n";
    check_result = ctx.check();
    ctx.display(std::cout);
    std::cout<<"--------------------------\n";
    std::cout<<((check_result==l_true) ? "satisfiable" : 
                (check_result==l_false) ? "unsatisfiable" : "unknown")<<"\n";
}
