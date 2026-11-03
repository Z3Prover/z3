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
#include "ast/for_each_expr.h"
#include "ast/proofs/proof_checker.h"
#include "ast/proofs/proof_utils.h"
#include "tactic/bv/dt2bv_tactic.h"
#include "tactic/tactic.h"
#include "tactic/tactical.h"
#include "tactic/core/split_clause_tactic.h"
#include "tactic/smtlogics/smt_tactic.h"
#include "smt/smt_solver.h"
#include "model/model_smt2_pp.h"
#include "model/model_evaluator.h"
#include "tactic/fd_solver/fd_solver.h"
#include "tactic/fd_solver/smtfd_solver.h"
#include "solver/solver2tactic.h"
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

static void test_fd_tactic_proof_boundary() {
    for (bool proofs : { false, true }) {
        ast_manager m(proofs ? PGM_ENABLED : PGM_DISABLED);
        reg_decl_plugins(m);
        params_ref p;
        expr_ref a = mk_bool(m, "proof_boundary_a");
        expr_ref not_a(m.mk_not(a), m);
        for (bool smtfd : { false, true }) {
            goal_ref g = alloc(goal, m, proofs, false, false);
            g->assert_expr(a);
            g->assert_expr(not_a);
            goal_ref_buffer result;
            bool failed = false;
            try {
                tactic_ref t = smtfd ? mk_smtfd_tactic(m, p) : mk_fd_tactic(m, p);
                (*t)(g, result);
            }
            catch (z3_exception const& ex) {
                failed = true;
                std::string message(ex.what());
                ENSURE(message.find("proof of false") != std::string::npos ||
                       message.find("does not support proof") != std::string::npos);
            }
            ENSURE(failed == proofs);
            if (proofs) {
                ENSURE(result.empty());
                ENSURE(!g->inconsistent());
                ENSURE(g->size() == 2);
            }
            else {
                ENSURE(result.size() == 1);
                ENSURE(result[0]->inconsistent());
            }
        }
    }
}

class proof_boundary_solver : public solver {
    lbool m_result;
    bool m_wrong_proof;
    expr_ref_vector m_assertions;
public:
    proof_boundary_solver(ast_manager& m, lbool result, bool wrong_proof):
        solver(m), m_result(result), m_wrong_proof(wrong_proof), m_assertions(m) {}
    solver* translate(ast_manager& m, params_ref const&) override {
        return alloc(proof_boundary_solver, m, m_result, m_wrong_proof);
    }
    void assert_expr_core(expr* e) override {
        m_assertions.push_back(m_result == l_undef ? m.mk_not(e) : e);
    }
    void assert_expr_core2(expr* e, expr*) override { assert_expr_core(e); }
    lbool check_sat_core(unsigned, expr* const*) override { return m_result; }
    proof* get_proof_core() override { return m_wrong_proof ? m.mk_asserted(m.mk_true()) : nullptr; }
    void get_model_core(model_ref& mdl) override { mdl = nullptr; }
    void collect_statistics_core(statistics&) const override {}
    void get_unsat_core(expr_ref_vector&) override {}
    std::string reason_unknown() const override { return "proof boundary test"; }
    void set_reason_unknown(char const*) override {}
    void get_labels(svector<symbol>&) override {}
    ast_manager& get_manager() const override { return m; }
    unsigned get_num_assertions() const override { return m_assertions.size(); }
    expr* get_assertion(unsigned i) const override { return m_assertions[i]; }
    unsigned get_num_assumptions() const override { return 0; }
    expr* get_assumption(unsigned) const override { return nullptr; }
    void push() override {}
    void pop(unsigned) override {}
    unsigned get_scope_level() const override { return 0; }
    void set_progress_callback(progress_callback*) override {}
    void set_phase(expr*) override {}
    void move_to_front(expr*) override {}
    phase* get_phase() override { return nullptr; }
    void set_phase(phase*) override {}
    expr_ref_vector cube(expr_ref_vector&, unsigned) override { return expr_ref_vector(m); }
    expr* congruence_root(expr* e) override { return e; }
    expr* congruence_next(expr* e) override { return e; }
    expr_ref congruence_explain(expr*, expr*) override { return expr_ref(m); }
    expr_ref_vector get_trail(unsigned) override { return expr_ref_vector(m); }
    void get_levels(ptr_vector<expr> const&, unsigned_vector&) override {}
};

static void test_solver2tactic_certificate_boundary() {
    ast_manager m(PGM_ENABLED);
    reg_decl_plugins(m);
    expr_ref a = mk_bool(m, "backend_certificate_a");
    for (bool wrong_proof : { false, true }) {
        tactic_ref t = mk_solver2tactic(alloc(proof_boundary_solver, m, l_false, wrong_proof));
        goal_ref g = alloc(goal, m, true, false, false);
        g->assert_expr(a);
        goal_ref_buffer result;
        bool failed = false;
        try {
            (*t)(g, result);
        }
        catch (tactic_exception const& ex) {
            failed = true;
            ENSURE(std::string(ex.what()).find("proof of false") != std::string::npos);
        }
        ENSURE(failed && result.empty());
        ENSURE(g->size() == 1 && g->form(0) == a && !g->inconsistent());
    }

    tactic_ref t = mk_solver2tactic(alloc(proof_boundary_solver, m, l_undef, true));
    goal_ref g = alloc(goal, m, true, false, false);
    g->assert_expr(a);
    proof_ref original_pr(m.mk_asserted(a), m);
    g->set(proof2proof_converter(m, original_pr));
    goal_ref_buffer result;
    (*t)(g, result);
    ENSURE(result.size() == 1 && result[0] == g.get());
    ENSURE(g->size() == 1 && g->form(0) == a);
    ENSURE(g->pr(0) == original_pr);
    ENSURE(g->get_reason_unknown() == "proof boundary test");
    ENSURE(g->pc());
    proof_ref converted = (*g->pc())(m, 0, nullptr);
    ENSURE(converted == original_pr);
}

static void test_solver2tactic_input_proofs() {
    ast_manager m(PGM_ENABLED);
    reg_decl_plugins(m);
    params_ref p;
    expr_ref a = mk_bool(m, "transport_a"), b = mk_bool(m, "transport_b");
    expr_ref original(m.mk_and(a, b), m), not_a(m.mk_not(a), m);
    proof_ref original_pr(m.mk_asserted(original), m);
    proof_ref a_pr(m.mk_and_elim(original_pr, 0), m);
    goal_ref g = alloc(goal, m, true, false, false);
    g->assert_expr(a, a_pr, nullptr);
    g->assert_expr(not_a);
    tactic_ref t = mk_solver2tactic(mk_smt_solver(m, p, symbol::null));
    goal_ref_buffer result;
    (*t)(g, result);
    ENSURE(result.size() == 1 && result[0]->inconsistent());
    proof_ref pr(result[0]->pr(0), m);
    ENSURE(pr && m.is_false(m.get_fact(pr)));
    bool found_original = false;
    auto check_leaf = [&](expr* e) {
        if (!m.is_asserted(e))
            return;
        expr* fact = m.get_fact(to_app(e));
        ENSURE(fact == original || fact == not_a);
        found_original |= fact == original;
    };
    for_each_expr(check_leaf, pr.get());
    ENSURE(found_original);
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

class tracking_proof_converter : public proof_converter {
    unsigned& m_calls;
    bool m_closed;
public:
    tracking_proof_converter(unsigned& calls, bool closed): m_calls(calls), m_closed(closed) {}

    proof_ref operator()(ast_manager& m, unsigned num_source, proof* const* source) override {
        ENSURE(num_source == 1 && source[0]);
        ENSURE(proof_utils::is_closed(m, source[0]) == m_closed);
        ++m_calls;
        return proof_ref(source[0], m);
    }

    proof_converter* translate(ast_translation&) override {
        return alloc(tracking_proof_converter, m_calls, m_closed);
    }

    void display(std::ostream& out) override { out << "(tracking-proof-converter)\n"; }
};

class register_proof_converter_tactic : public tactic {
    unsigned& m_calls;
    bool m_closed;
public:
    register_proof_converter_tactic(unsigned& calls, bool closed): m_calls(calls), m_closed(closed) {}

    void operator()(goal_ref const& in, goal_ref_buffer& result) override {
        if (in->proofs_enabled())
            in->add(alloc(tracking_proof_converter, m_calls, m_closed));
        result.push_back(in.get());
    }

    tactic* translate(ast_manager&) override {
        return alloc(register_proof_converter_tactic, m_calls, m_closed);
    }

    void cleanup() override {}
    char const* name() const override { return "register-proof-converter"; }
};

static void test_split_proof_converters() {
    for (bool proofs : {false, true}) {
        for (unsigned composition : {0u, 1u, 2u}) {
            ast_manager m(proofs ? PGM_ENABLED : PGM_DISABLED);
            reg_decl_plugins(m);
            unsigned parent_calls = 0, branch_calls = 0;
            goal_ref input = alloc(goal, m, proofs, true, false);
            expr_ref a = mk_bool(m, "split-a"), b = mk_bool(m, "split-b");
            expr_ref clause(m.mk_or(a, b), m), not_a(m.mk_not(a), m), not_b(m.mk_not(b), m);
            input->assert_expr(clause);
            input->assert_expr(not_a);
            input->assert_expr(not_b);
            if (proofs)
                input->add(alloc(tracking_proof_converter, parent_calls, true));

            tactic_ref split = mk_split_clause_tactic();
            tactic_ref register_pc = alloc(register_proof_converter_tactic, branch_calls, composition == 2);
            tactic_ref smt = mk_smt_tactic(m);
            tactic_ref solve_branch = and_then(register_pc.get(), smt.get());
            tactic_ref pipeline;
            if (composition == 0)
                pipeline = and_then(split.get(), solve_branch.get());
            else if (composition == 1) {
                tactic_ref step = or_else(split.get(), solve_branch.get());
                pipeline = repeat(step.get(), 4);
            }
            else
                pipeline = solve_branch;

            model_ref model;
            labels_vec labels;
            proof_ref proof(m);
            expr_dependency_ref core(m);
            std::string reason;
            ENSURE(check_sat(*pipeline, input, model, labels, proof, core, reason) == l_false);
            ENSURE(parent_calls == (proofs ? 1u : 0u));
            ENSURE(branch_calls == (proofs ? (composition == 2 ? 1u : 2u) : 0u));
            if (proofs) {
                ENSURE(proof && m.is_false(m.get_fact(proof)) && proof_utils::is_closed(m, proof));
                auto check_leaves = [&](expr* e) {
                    if (m.is_asserted(e)) {
                        expr* fact = m.get_fact(to_app(e));
                        ENSURE(fact == clause || fact == not_a || fact == not_b);
                    }
                };
                for_each_expr(check_leaves, proof);
                proof_checker checker(m);
                expr_ref_vector conditions(m);
                ENSURE(checker.check(proof, conditions));
                ENSURE(conditions.empty());
                tactic_ref skip = mk_skip_tactic();
                ENSURE(check_sat(*skip, input, model, labels, proof, core, reason) == l_false);
                ENSURE(parent_calls == 1);
                ENSURE(branch_calls == (composition == 2 ? 1u : 2u));
            }
            else
                ENSURE(!proof);
        }
    }
}

void tst_get_consequences() {
    test_fd_tactic_proof_boundary();
    test_solver2tactic_certificate_boundary();
    test_solver2tactic_input_proofs();
    test1();
    test2();
    test_bounded_int();
    test_bounded_int_translation();
    test_cardinality_consequences_after_check();
    test_datatype_accessor_consequences();
    test_split_proof_converters();
}
