
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "ast/proofs/proof_checker.h"
#include "ast/ast_ll_pp.h"
#include "ast/reg_decl_plugins.h"
#include "sat/smt/euf_proof_checker.h"
#include <iostream>

void tst_checker1() {
    ast_manager m(PGM_ENABLED);
    expr_ref a(m);
    proof_ref p1(m), p2(m), p3(m), p4(m);
    expr_ref_vector side_conditions(m);

    a = m.mk_const(symbol("a"), m.mk_bool_sort());
    p1 = m.mk_hypothesis(a.get());
    p2 = m.mk_hypothesis(m.mk_not(a.get()));
    ast_ll_pp(std::cout, m, p1.get());
    ast_ll_pp(std::cout, m, p2.get());
    proof* proofs[2] = { p1.get(), p2.get() };
    p3 = m.mk_unit_resolution(2, proofs);
    p4 = m.mk_lemma(p3.get(), a.get());
    ast_ll_pp(std::cout, m, p4.get());
    proof_checker checker(m);
    p4 = m.mk_lemma(p3.get(), m.mk_or(a.get(), m.mk_not(a.get())));
    ast_ll_pp(std::cout, m, p4.get());
    VERIFY(checker.check(p4.get(), side_conditions));
}

void tst_initializer_list_overloads() {
    ast_manager m(PGM_ENABLED);
    expr_ref a(m), b(m);
    proof_ref p1(m), p2(m), p3(m), p4(m);
    expr_ref_vector side_conditions(m);

    // Test mk_unit_resolution with initializer_list
    a = m.mk_const(symbol("a"), m.mk_bool_sort());
    b = m.mk_const(symbol("b"), m.mk_bool_sort());
    p1 = m.mk_hypothesis(a.get());
    p2 = m.mk_hypothesis(m.mk_not(a.get()));
    
    // Test the new initializer_list overload - should produce false
    p3 = m.mk_unit_resolution({ p1.get(), p2.get() });
    VERIFY(m.get_fact(p3.get()) == m.mk_false());
    
    // Test mk_unit_resolution with new_fact parameter
    expr_ref fact(m.mk_or(a.get(), b.get()), m);
    proof_ref pa_or_b(m.mk_hypothesis(fact.get()), m);
    proof_ref pnot_a(m.mk_hypothesis(m.mk_not(a.get())), m);
    p4 = m.mk_unit_resolution({ pa_or_b.get(), pnot_a.get() }, b.get());
    VERIFY(m.get_fact(p4.get()) == b.get());
    
    // Test mk_transitivity with initializer_list
    // Create a simple transitivity chain: a = b, b = c => a = c
    expr_ref c(m);
    c = m.mk_const(symbol("c"), m.mk_bool_sort());
    
    // Create rewrite proofs for a = b and b = c
    proof_ref pr_ab(m.mk_rewrite(a.get(), b.get()), m);
    proof_ref pr_bc(m.mk_rewrite(b.get(), c.get()), m);
    
    // Test the new initializer_list overload for transitivity
    // This should create a proof of a = c
    proof_ref p5(m.mk_transitivity({ pr_ab.get(), pr_bc.get() }), m);
    VERIFY(p5.get() != nullptr);
    // Verify the result is a proof with the expected fact (a = c)
    expr* trans_fact = m.get_fact(p5.get());
    VERIFY(m.is_eq(trans_fact));
    VERIFY(to_app(trans_fact)->get_arg(0) == a.get());
    VERIFY(to_app(trans_fact)->get_arg(1) == c.get());
    
    std::cout << "Initializer list overloads test passed!" << std::endl;
}

static void tst_euf_negation() {
    ast_manager m;
    reg_decl_plugins(m);
    euf::theory_checker checker(m);
    expr_ref x(m.mk_const(symbol("x"), m.mk_bool_sort()), m);
    expr_ref y(m.mk_const(symbol("y"), m.mk_bool_sort()), m);
    expr_ref nx(m.mk_not(x), m);
    expr_ref eq(m.mk_eq(nx, y), m);
    auto check = [&](std::initializer_list<expr*> args) {
        expr_ref hint(m.mk_app(symbol("euf"), args.size(), args.begin(), m.mk_proof_sort()), m);
        return checker.check(hint);
    };

    VERIFY(check({m.mk_eq(x, nx)}));
    VERIFY(!check({eq, y}));
    VERIFY(check({x, eq, y}));
    VERIFY(!check({x, eq, m.mk_not(y)}));
    VERIFY(check({nx, eq, m.mk_not(y)}));
    VERIFY(!check({nx, eq, y}));
}

static void tst_euf_negation_large_classes() {
    ast_manager m;
    reg_decl_plugins(m);
    euf::theory_checker checker(m);
    expr_ref x(m.mk_const(symbol("x"), m.mk_bool_sort()), m);
    expr_ref nx(m.mk_not(x), m);
    expr_ref_vector args(m);
    // Both classes lack truth values, so per-negation class scans are quadratic.
    for (unsigned i = 0; i < 16384; ++i) {
        expr_ref y(m.mk_fresh_const("y", m.mk_bool_sort()), m);
        args.push_back(m.mk_eq(x, y));
        args.push_back(m.mk_eq(nx, m.mk_not(y)));
    }
    expr_ref hint(m.mk_app(symbol("euf"), args.size(), args.data(), m.mk_proof_sort()), m);
    VERIFY(!checker.check(hint));
    args.push_back(m.mk_false());
    hint = m.mk_app(symbol("euf"), args.size(), args.data(), m.mk_proof_sort());
    VERIFY(checker.check(hint));
}

void tst_proof_checker() {
    tst_checker1();
    tst_initializer_list_overloads();
    tst_euf_negation();
    tst_euf_negation_large_classes();
}
