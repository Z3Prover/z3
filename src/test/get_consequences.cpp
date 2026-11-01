/*++
Copyright (c) 2016 Microsoft Corporation

--*/

#include "sat/sat_solver/inc_sat_solver.h"
#include "ast/bv_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/pb_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_pp.h"
#include "tactic/bv/dt2bv_tactic.h"
#include "tactic/bv/dt2bv_proof_converter.h"
#include "ast/converters/proof_converter.h"
#include "ast/for_each_expr.h"
#include "ast/proofs/proof_checker.h"
#include "ast/proofs/proof_utils.h"
#include "params/smt_params.h"
#include "smt/smt_kernel.h"
#include "tactic/tactic.h"
#include "tactic/tactical.h"
#include "tactic/core/split_clause_tactic.h"
#include "tactic/smtlogics/smt_tactic.h"
#include "smt/smt_solver.h"
#include "model/model_smt2_pp.h"
#include "model/model_evaluator.h"
#include "tactic/fd_solver/fd_solver.h"
#include <iostream>
#include <string>

static expr_ref mk_const(ast_manager& m, char const* name, sort* s) {
    return expr_ref(m.mk_const(symbol(name), s), m);
}

static expr_ref mk_bool(ast_manager& m, char const* name) {
    return expr_ref(m.mk_const(symbol(name), m.mk_bool_sort()), m);
}

static expr_ref mk_bv(ast_manager& m, char const* name, unsigned sz) {
    bv_util bv(m);
    return expr_ref(m.mk_const(symbol(name), bv.mk_sort(sz)), m);
}

static void test1() {
    ast_manager m;
    reg_decl_plugins(m);
    bv_util bv(m);
    params_ref p;

    ref<solver> solver = mk_inc_sat_solver(m, p);
    expr_ref a = mk_bool(m, "a"), b = mk_bool(m, "b"), c = mk_bool(m, "c");
    expr_ref ba = mk_bv(m, "ba", 3), bb = mk_bv(m, "bb", 3), bc = mk_bv(m, "bc", 3);

    solver->assert_expr(m.mk_implies(a, b));
    solver->assert_expr(m.mk_implies(b, c));
    expr_ref_vector asms(m), vars(m), conseq(m);
    asms.push_back(a);
    vars.push_back(b);
    vars.push_back(c);
    vars.push_back(bb);
    vars.push_back(bc);
    solver->assert_expr(m.mk_eq(ba, bc));
    solver->assert_expr(m.mk_eq(bv.mk_numeral(2, 3), ba));
    solver->get_consequences(asms, vars, conseq);

    std::cout << conseq << "\n";
}


void test2() {
    ast_manager m;
    reg_decl_plugins(m);
    bv_util bv(m);
    datatype_util dtutil(m);
    params_ref p;

    datatype_decl_plugin & dt = *(static_cast<datatype_decl_plugin*>(m.get_plugin(m.get_family_id("datatype"))));
    sort_ref_vector new_sorts(m);
    constructor_decl* R = mk_constructor_decl(symbol("R"), symbol("is-R"), 0, nullptr);
    constructor_decl* G = mk_constructor_decl(symbol("G"), symbol("is-G"), 0, nullptr);
    constructor_decl* B = mk_constructor_decl(symbol("B"), symbol("is-B"), 0, nullptr);
    constructor_decl* constrs[3] = { R, G, B };
    datatype_decl * enum_sort = mk_datatype_decl(dtutil, symbol("RGB"), 0, nullptr, 3, constrs);
    VERIFY(dt.mk_datatypes(1, &enum_sort, 0, nullptr, new_sorts));
    sort* rgb = new_sorts[0].get();

    expr_ref x = mk_const(m, "x", rgb), y = mk_const(m, "y", rgb), z = mk_const(m, "z", rgb);
    ptr_vector<func_decl> const& enums = *dtutil.get_datatype_constructors(rgb);
    expr_ref r = expr_ref(m.mk_const(enums[0]), m);
    expr_ref g = expr_ref(m.mk_const(enums[1]), m);
    expr_ref b = expr_ref(m.mk_const(enums[2]), m);

    ref<solver> fd_solver = mk_fd_solver(m, p);
    fd_solver->assert_expr(m.mk_not(m.mk_eq(x, r)));
    fd_solver->assert_expr(m.mk_not(m.mk_eq(x, b)));

    expr_ref_vector asms(m), vars(m), conseq(m);
    vars.push_back(x);
    vars.push_back(y);

    VERIFY(l_true == fd_solver->get_consequences(asms, vars, conseq));
    ENSURE(!conseq.empty());
    std::cout << conseq << "\n";
    conseq.reset();

    ast_manager dst;
    reg_decl_plugins(dst);
    ref<solver> translated_solver = fd_solver->translate(dst, p);
    ast_translation tr(m, dst);
    expr_ref translated_x(tr(x.get()), dst);
    expr_ref translated_g(tr(g.get()), dst);

    VERIFY(l_true == translated_solver->check_sat(0, nullptr));
    model_ref mr;
    translated_solver->get_model(mr);
    ENSURE(mr.get());
    model_evaluator eval(*mr);
    expr_ref value(dst);
    eval(translated_x, value);
    ENSURE(dst.are_equal(value, translated_g));
    model_smt2_pp(std::cout << "model:\n", dst, *mr.get(), 0);

    VERIFY(l_true == translated_solver->check_sat(0,nullptr));
    translated_solver->get_model(mr);
    ENSURE(mr.get());
    model_smt2_pp(std::cout, dst, *mr.get(), 0);

}

static void test_bounded_int_translation() {
    ast_manager source;
    reg_decl_plugins(source);
    params_ref p;
    ref<solver> source_solver = mk_fd_solver(source, p);
    arith_util source_arith(source);
    expr_ref source_x = mk_const(source, "x", source_arith.mk_int());
    expr_ref source_three(source_arith.mk_int(3), source);
    expr_ref source_zero(source_arith.mk_int(0), source);
    expr_ref source_five(source_arith.mk_int(5), source);
    source_solver->assert_expr(source_arith.mk_le(source_zero, source_x));
    source_solver->assert_expr(source_arith.mk_le(source_x, source_five));
    source_solver->assert_expr(source.mk_eq(source_x, source_three));
    VERIFY(l_true == source_solver->check_sat(0, nullptr));

    ast_manager m;
    reg_decl_plugins(m);
    ref<solver> fd_solver = source_solver->translate(m, p);
    ast_translation tr(source, m);
    arith_util arith(m);
    expr_ref x(tr(source_x.get()), m);
    expr_ref three(arith.mk_int(3), m);

    VERIFY(l_true == fd_solver->check_sat(0, nullptr));

    model_ref mdl;
    fd_solver->get_model(mdl);
    ENSURE(mdl.get());
    model_evaluator eval(*mdl);
    expr_ref value(m);
    eval(x, value);
    ENSURE(m.are_equal(value, three));

    VERIFY(l_true == fd_solver->check_sat(0, nullptr));
}

static void test_bounded_int() {
    ast_manager source;
    reg_decl_plugins(source);
    params_ref p;
    ref<solver> source_solver = mk_fd_solver(source, p);

    ast_manager m;
    reg_decl_plugins(m);
    ref<solver> fd_solver = source_solver->translate(m, p);
    arith_util arith(m);
    expr_ref x = mk_const(m, "x", arith.mk_int());
    expr_ref three(arith.mk_int(3), m);
    expr_ref four(arith.mk_int(4), m);
    expr_ref zero(arith.mk_int(0), m);
    expr_ref five(arith.mk_int(5), m);

    fd_solver->assert_expr(arith.mk_le(zero, x));
    fd_solver->assert_expr(arith.mk_le(x, five));
    fd_solver->assert_expr(m.mk_eq(x, three));

    expr_ref_vector asms(m), vars(m), conseq(m);
    vars.push_back(x);
    VERIFY(l_true == fd_solver->get_consequences(asms, vars, conseq));
    ENSURE(!conseq.empty());

    fd_solver->push();
    fd_solver->assert_expr(m.mk_eq(x, four));
    VERIFY(l_false == fd_solver->check_sat(0, nullptr));
    fd_solver->pop(1);
    VERIFY(l_true == fd_solver->check_sat(0, nullptr));
}

static void test_cardinality_consequences_after_check() {
    ast_manager m;
    reg_decl_plugins(m);
    params_ref p;
    p.set_sym("phase", symbol("always_true"));
    ref<solver> fd_solver = mk_fd_solver(m, p);
    pb_util pb(m);

    expr_ref_vector as(m), xs(m), clause(m);
    for (unsigned i = 0; i < 5; ++i) {
        as.push_back(mk_bool(m, ("a" + std::to_string(i)).c_str()));
    }
    for (unsigned i = 0; i < 8; ++i) {
        xs.push_back(mk_bool(m, ("x" + std::to_string(i)).c_str()));
    }
    expr_ref y = mk_bool(m, "y");

    fd_solver->assert_expr(pb.mk_at_most_k(as.size(), as.data(), 1));
    fd_solver->assert_expr(m.mk_or(xs.size(), xs.data()));
    fd_solver->assert_expr(pb.mk_at_most_k(xs.size(), xs.data(), 1));
    for (unsigned i = 0; i < xs.size(); ++i) {
        if (i != 5) clause.push_back(xs[i].get());
    }
    clause.push_back(m.mk_not(y));
    fd_solver->assert_expr(m.mk_or(clause));
    VERIFY(l_true == fd_solver->check_sat(0, nullptr));
    model_ref mdl;
    fd_solver->get_model(mdl);
    model_evaluator eval(*mdl);
    expr_ref value(m);
    eval(y, value);
    ENSURE(m.is_true(value));

    expr_ref_vector asms(m), vars(m), conseq(m);
    asms.push_back(xs[5].get());
    vars.push_back(y);
    VERIFY(l_true == fd_solver->get_consequences(asms, vars, conseq));
    ENSURE(conseq.size() == 1);
    ENSURE(m.are_equal(conseq[0].get(), m.mk_implies(xs[5].get(), m.mk_not(y))));

    expr_ref_vector check_asms(m);
    check_asms.push_back(xs[5].get());
    check_asms.push_back(y);
    VERIFY(l_false == fd_solver->check_sat(check_asms));
}

static void test_datatype_accessor_consequences() {
    ast_manager m;
    reg_decl_plugins(m);
    datatype_util dt(m);
    arith_util arith(m);
    params_ref p;

    accessor_decl* accessors[] = { mk_accessor_decl(m, symbol("val"), type_ref(arith.mk_int())) };
    constructor_decl* constructors[] = {
        mk_constructor_decl(symbol("none"), symbol("is-none"), 0, nullptr),
        mk_constructor_decl(symbol("some"), symbol("is-some"), 1, accessors)
    };
    datatype_decl* option = mk_datatype_decl(dt, symbol("Option_Int"), 0, nullptr, 2, constructors);
    sort_ref_vector sorts(m);
    VERIFY(dt.plugin().mk_datatypes(1, &option, 0, nullptr, sorts));
    sort* option_sort = sorts[0].get();
    func_decl* val = (*dt.get_constructor_accessors((*dt.get_datatype_constructors(option_sort))[1]))[0];

    expr_ref a = mk_const(m, "a", option_sort);
    expr_ref b = mk_const(m, "b", option_sort);
    expr_ref t0 = mk_bool(m, "t0");
    expr_ref t1 = mk_bool(m, "t1");
    expr_ref va(m.mk_app(val, a), m);
    expr_ref vb(m.mk_app(val, b), m);
    expr_ref two(arith.mk_int(2), m);
    expr_ref nine(arith.mk_int(9), m);
    ref<solver> smt_solver = mk_smt_solver(m, p, symbol::null);
    smt_solver->assert_expr(m.mk_implies(t0, m.mk_eq(va, two)));
    smt_solver->assert_expr(m.mk_implies(t1, m.mk_eq(vb, nine)));

    expr_ref_vector assumptions(m), vars(m), consequences(m);
    assumptions.push_back(t0);
    assumptions.push_back(t1);
    vars.push_back(va);
    vars.push_back(vb);
    VERIFY(l_true == smt_solver->get_consequences(assumptions, vars, consequences));
    ENSURE(consequences.size() == 2);
    expr_ref expected_a(m.mk_implies(t0, m.mk_eq(va, two)), m);
    expr_ref expected_b(m.mk_implies(t1, m.mk_eq(vb, nine)), m);
    bool found_a = false, found_b = false;
    for (expr* consequence : consequences) {
        found_a |= m.are_equal(consequence, expected_a);
        found_b |= m.are_equal(consequence, expected_b);
    }
    ENSURE(found_a && found_b);
}

static void check_dt2bv_proof(ast_manager& m, proof* proof, obj_hashtable<expr> const& originals) {
    bv_util bv(m);
    ENSURE(proof && m.is_false(m.get_fact(proof)) && proof_utils::is_closed(m, proof));
    auto check_leaves = [&](expr* e) {
        if (m.is_asserted(e))
            ENSURE(originals.contains(m.get_fact(to_app(e))));
        ENSURE(!is_uninterp_const(e) || !bv.is_bv(e));
    };
    for_each_expr(check_leaves, proof);
    proof_checker checker(m);
    expr_ref_vector conditions(m);
    ENSURE(checker.check(proof, conditions));
    for (expr* condition : conditions) {
        smt_params params;
        smt::kernel check(m, params);
        expr_ref negation(m.mk_not(condition), m);
        check.assert_expr(negation);
        ENSURE(check.check() == l_false);
    }
}

class counting_proof_converter : public proof_converter {
    unsigned& m_calls;
public:
    counting_proof_converter(unsigned& calls): m_calls(calls) {}

    proof_ref operator()(ast_manager& m, unsigned num_source, proof* const* source) override {
        ENSURE(num_source == 1 && source[0] && proof_utils::is_closed(m, source[0]));
        bv_util bv(m);
        auto check_encoding = [&](expr* e) { ENSURE(!is_uninterp_const(e) || !bv.is_bv(e)); };
        for_each_expr(check_encoding, source[0]);
        ++m_calls;
        return proof_ref(source[0], m);
    }

    proof_converter* translate(ast_translation&) override {
        return alloc(counting_proof_converter, m_calls);
    }

    void display(std::ostream& out) override { out << "(counting-proof-converter)\n"; }
};

static void test_dt2bv_proofs() {
    for (unsigned count : {1u, 2u, 3u, 5u}) {
        ast_manager m(PGM_ENABLED);
        reg_decl_plugins(m);
        datatype_util dt(m);
        bv_util bv(m);
        ptr_vector<constructor_decl> declarations;
        for (unsigned i = 0; i < count; ++i)
            declarations.push_back(mk_constructor_decl(symbol(i), symbol(i + count), 0, nullptr));
        datatype_decl* enumeration = mk_datatype_decl(dt, symbol("Enum"), 0, nullptr,
                                                      count, declarations.data());
        sort_ref_vector sorts(m);
        ENSURE(dt.plugin().mk_datatypes(1, &enumeration, 0, nullptr, sorts));
        expr_ref x = mk_const(m, "x", sorts.get(0));
        auto const& constructors = *dt.get_datatype_constructors(sorts.get(0));
        goal_ref input = alloc(goal, m, true, true, false);
        obj_hashtable<expr> originals;
        for (func_decl* constructor : constructors) {
            expr_ref value(m.mk_const(constructor), m);
            expr_ref equation(m.mk_eq(x, value), m);
            expr_ref assertion(m.mk_not(equation), m);
            originals.insert(assertion);
            input->assert_expr(assertion);
        }
        tactic_ref tactic = mk_dt2bv_tactic(m);
        goal_ref_buffer result;
        (*tactic)(input, result);
        ENSURE(result.size() == 1);
        proof_converter_ref converter = result[0]->pc();
        ENSURE(converter);
        ref<solver> backend = mk_smt_solver(m, params_ref(), symbol::null);
        for (unsigned i = 0; i < result[0]->size(); ++i)
            backend->assert_expr(result[0]->form(i));
        ENSURE(backend->check_sat(0, nullptr) == l_false);
        proof_ref proof(backend->get_proof(), m);
        apply(m, converter.get(), proof);
        check_dt2bv_proof(m, proof, originals);

        ast_manager target(PGM_ENABLED);
        reg_decl_plugins(target);
        ast_translation translation(m, target);
        proof_converter_ref translated = converter->translate(translation);
        proof_ref target_proof(translation(backend->get_proof()), target);
        apply(target, translated.get(), target_proof);
        obj_hashtable<expr> target_originals;
        for (expr* original : originals)
            target_originals.insert(translation(original));
        check_dt2bv_proof(target, target_proof, target_originals);

        proof_ref foreign(m.mk_asserted(m.mk_false()), m);
        bool rejected = false;
        try { apply(m, converter.get(), foreign); }
        catch (tactic_exception const&) { rejected = true; }
        ENSURE(rejected);

        if (count > 1) {
            expr_ref first(m.mk_const(constructors[0]), m), second(m.mk_const(constructors[1]), m);
            expr_ref eq_first(m.mk_eq(x, first), m), eq_second(m.mk_eq(x, second), m);
            expr_ref clause(m.mk_or(eq_first, eq_second), m);
            originals.insert(clause);
            for (unsigned composition : {0u, 1u, 2u}) {
                unsigned conversions = 0;
                goal_ref branch = alloc(goal, m, true, true, false);
                branch->add(alloc(counting_proof_converter, conversions));
                branch->assert_expr(clause);
                branch->assert_expr(m.mk_not(eq_first));
                branch->assert_expr(m.mk_not(eq_second));
                tactic_ref encode = mk_dt2bv_tactic(m);
                tactic_ref split = mk_split_clause_tactic();
                tactic_ref smt = mk_smt_tactic(m);
                tactic_ref pipeline;
                if (composition == 0)
                    pipeline = and_then(encode.get(), split.get(), smt.get());
                else if (composition == 1)
                    pipeline = and_then(split.get(), encode.get(), smt.get());
                else {
                    tactic_ref step = or_else(split.get(), smt.get());
                    tactic_ref repeated = repeat(step.get(), 4);
                    pipeline = and_then(encode.get(), repeated.get());
                }
                model_ref model;
                labels_vec labels;
                expr_dependency_ref core(m);
                std::string reason;
                ENSURE(check_sat(*pipeline, branch, model, labels, proof, core, reason) == l_false);
                ENSURE(conversions == 1);
                check_dt2bv_proof(m, proof, originals);
            }
            goal_ref no_proofs = alloc(goal, m, false, true, false);
            no_proofs->assert_expr(clause);
            no_proofs->assert_expr(m.mk_not(eq_first));
            no_proofs->assert_expr(m.mk_not(eq_second));
            tactic_ref encode = mk_dt2bv_tactic(m);
            tactic_ref split = mk_split_clause_tactic();
            tactic_ref smt = mk_smt_tactic(m);
            tactic_ref pipeline = and_then(encode.get(), split.get(), smt.get());
            model_ref model;
            labels_vec labels;
            expr_dependency_ref core(m);
            std::string reason;
            ENSURE(check_sat(*pipeline, no_proofs, model, labels, proof, core, reason) == l_false);
            ENSURE(!proof && !no_proofs->pc());
        }

        if (count == 2) {
            expr_ref fresh = mk_bv(m, "binding", 1);
            expr_ref first(m.mk_const(constructors[0]), m);
            expr_ref condition(m.mk_eq(x, first), m);
            expr_ref zero(bv.mk_numeral(0, 1), m), one(bv.mk_numeral(1, 1), m);
            expr_ref encoding(m.mk_ite(condition, zero, one), m);
            sort* domain = fresh->get_sort();
            symbol name("z");
            func_decl_ref predicate(m.mk_func_decl(symbol("P"), 1, &domain, m.mk_bool_sort()), m);
            expr_ref variable(m.mk_var(0, domain), m);
            expr_ref body(m.mk_app(predicate.get(), variable), m);
            expr_ref quantified(m.mk_forall(1, &domain, &name, body), m);
            expr_ref instance(m.mk_app(predicate.get(), fresh), m);
            expr_ref encoded_instance(m.mk_app(predicate.get(), encoding), m);
            expr_ref original_not(m.mk_not(encoded_instance), m);
            expr_ref instance_clause(m.mk_or(m.mk_not(quantified), instance), m);
            expr* binding = fresh;
            proof_ref instantiation(m.mk_quant_inst(instance_clause, 1, &binding), m);
            proof_ref universal(m.mk_asserted(quantified), m);
            proof_ref negated(m.mk_asserted(m.mk_not(instance)), m);
            proof = m.mk_unit_resolution({instantiation, universal, negated}, m.mk_false());
            dt2bv_proof_converter parameters(m);
            parameters.insert_enum(to_app(x)->get_decl(), to_app(fresh)->get_decl());
            parameters.insert(universal, quantified);
            proof_ref original(m.mk_asserted(original_not), m);
            parameters.insert(original, m.mk_not(instance));
            apply(m, &parameters, proof);
            obj_hashtable<expr> parameter_originals;
            parameter_originals.insert(quantified);
            parameter_originals.insert(original_not);
            check_dt2bv_proof(m, proof, parameter_originals);
            bool found = false;
            auto check_binding = [&](expr* e) {
                if (m.is_quant_inst(e)) {
                    found = true;
                    auto const& parameter = to_app(e)->get_decl()->get_parameter(0);
                    ENSURE(parameter.is_ast() && parameter.get_ast() == encoding);
                }
            };
            for_each_expr(check_binding, proof);
            ENSURE(found);
            parameter payload[] = {parameter(symbol("bv")), parameter(to_app(fresh)->get_decl())};
            expr* false_fact = m.mk_false();
            proof_ref unsupported(m.mk_app(m.get_basic_family_id(), PR_TH_LEMMA, 2, payload,
                                            1, &false_fact), m);
            rejected = false;
            try { apply(m, &parameters, unsupported); }
            catch (tactic_exception const&) { rejected = true; }
            ENSURE(rejected);
        }

        if (count == 3) {
            dt2bv_proof_converter bad(m);
            expr_ref fresh = mk_bv(m, "bad", 2);
            bad.insert_enum(to_app(x)->get_decl(), to_app(fresh)->get_decl());
            expr_ref numeral(bv.mk_numeral(0, 2), m);
            expr_ref wrong(m.mk_eq(fresh, numeral), m);
            expr_ref value(m.mk_const(constructors[0]), m);
            expr_ref equation(m.mk_eq(x, value), m);
            proof_ref original(m.mk_asserted(m.mk_not(equation)), m);
            rejected = false;
            try { bad.insert(original, wrong); }
            catch (tactic_exception const&) { rejected = true; }
            ENSURE(rejected);
        }
    }
}

void tst_get_consequences() {
    test1();
    test2();
    test_bounded_int();
    test_bounded_int_translation();
    test_cardinality_consequences_after_check();
    test_datatype_accessor_consequences();
    test_dt2bv_proofs();
}
