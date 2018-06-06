/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "util/trace.h"
#include "util/vector.h"
#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "util/statistics.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/pb2bv_rewriter.h"
#include "smt/smt_kernel.h"
#include "model/model_smt2_pp.h"
#include "smt/params/smt_params.h"
#include "ast/ast_util.h"
#include "ast/pb_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "tactic/portfolio/fd_solver.h"
#include "solver/solver.h"

static void test1() {
    ast_manager m;
    reg_decl_plugins(m);
    pb_util pb(m);
    params_ref p;
    pb2bv_rewriter rw(m, p);
    expr_ref_vector vars(m);
    unsigned N = 5;
    for (unsigned i = 0; i < N; ++i) {
        std::stringstream strm;
        strm << "b" << i;
        vars.push_back(m.mk_const(symbol(strm.str().c_str()), m.mk_bool_sort()));
    }
    
    for (unsigned k = 1; k <= N; ++k) {
        expr_ref fml(m), result(m);
        proof_ref proof(m);
        fml = pb.mk_at_least_k(vars.size(), vars.c_ptr(), k);
        rw(true, fml, result, proof);
        std::cout << fml << " |-> " << result << "\n";
    }
    expr_ref_vector lemmas(m);
    rw.flush_side_constraints(lemmas);
    std::cout << lemmas << "\n";
}

static void test_semantics(ast_manager& m, expr_ref_vector const& vars, vector<rational> const& coeffs, unsigned k, unsigned kind) {
    pb_util pb(m);
    params_ref p;
    pb2bv_rewriter rw(m, p);
    unsigned N = vars.size();
    expr_ref fml1(m), fml2(m), result1(m), result2(m);
    proof_ref proof(m);
    expr_ref_vector lemmas(m);
    th_rewriter th_rw(m);

    switch (kind) {
    case 0: fml1 = pb.mk_ge(vars.size(), coeffs.c_ptr(), vars.c_ptr(), rational(k)); break;
    case 1: fml1 = pb.mk_le(vars.size(), coeffs.c_ptr(), vars.c_ptr(), rational(k)); break;
    default: fml1 = pb.mk_eq(vars.size(), coeffs.c_ptr(), vars.c_ptr(), rational(k)); break;
    }
    rw(true, fml1, result1, proof);
    rw.flush_side_constraints(lemmas);
    std::cout << "lemmas: " << lemmas << "\n";
    std::cout << "simplified: " << result1 << "\n";
    for (unsigned values = 0; values < static_cast<unsigned>(1 << N); ++values) {
        smt_params fp;
        smt::kernel solver(m, fp);
        expr_ref_vector tf(m);
        for (unsigned i = 0; i < N; ++i) {
            bool is_true = 0 != (values & (1 << i));
            tf.push_back(is_true ? m.mk_true() : m.mk_false());
            solver.assert_expr(is_true ? vars[i] : m.mk_not(vars[i]));
        }
        
        solver.assert_expr(lemmas);
        switch (kind) {
        case 0: fml2 = pb.mk_ge(tf.size(), coeffs.c_ptr(), tf.c_ptr(), rational(k)); break;
        case 1: fml2 = pb.mk_le(tf.size(), coeffs.c_ptr(), tf.c_ptr(), rational(k)); break;
        default: fml2 = pb.mk_eq(tf.size(), coeffs.c_ptr(), tf.c_ptr(), rational(k)); break;
        }
        std::cout << fml1 << " " << fml2 << "\n";
        th_rw(fml2, result2, proof);
        ENSURE(m.is_true(result2) || m.is_false(result2));
        lbool res = solver.check();
        VERIFY(res == l_true);
        solver.assert_expr(m.is_true(result2) ? m.mk_not(result1) : result1.get());
        res = solver.check();
        if (res != l_false) {
            IF_VERBOSE(0, solver.display(verbose_stream());
                       verbose_stream() << vars << " k: " << k << " kind: " << kind << "\n";
                       for (auto const& c : coeffs) verbose_stream() << c << "\n";
                       );
        }
        VERIFY(res == l_false);
    }
}

static void test_semantics(ast_manager& m, expr_ref_vector const& vars, vector<rational> const& coeffs, unsigned k) {
    test_semantics(m, vars, coeffs, k, 0);
    test_semantics(m, vars, coeffs, k, 1);
    test_semantics(m, vars, coeffs, k, 2);
}

static void test2() {
    ast_manager m;
    reg_decl_plugins(m);
    expr_ref_vector vars(m);
    unsigned N = 4;
    for (unsigned i = 0; i < N; ++i) {
        std::stringstream strm;
        strm << "b" << i;
        vars.push_back(m.mk_const(symbol(strm.str().c_str()), m.mk_bool_sort()));
    }
    for (unsigned coeff = 0; coeff < static_cast<unsigned>(1 << N); ++coeff) {
        vector<rational> coeffs;
        for (unsigned i = 0; i < N; ++i) {
            bool is_one = 0 != (coeff & (1 << i));
            coeffs.push_back(is_one ? rational(1) : rational(2));
        }
        for (unsigned i = 0; i <= N; ++i) {
            test_semantics(m, vars, coeffs, i);
        }
    }
}


static void test_solver_semantics(ast_manager& m, expr_ref_vector const& vars, vector<rational> const& coeffs, unsigned k, unsigned kind) {
    pb_util pb(m);
    params_ref p;
    unsigned N = vars.size();
    expr_ref fml1(m), fml2(m), result1(m), result2(m);
    proof_ref proof(m);
    th_rewriter th_rw(m);

    switch (kind) {
    case 0: fml1 = pb.mk_ge(vars.size(), coeffs.c_ptr(), vars.c_ptr(), rational(k)); break;
    case 1: fml1 = pb.mk_le(vars.size(), coeffs.c_ptr(), vars.c_ptr(), rational(k)); break;
    default: fml1 = pb.mk_eq(vars.size(), coeffs.c_ptr(), vars.c_ptr(), rational(k)); break;
    }
    result1 = m.mk_fresh_const("xx", m.mk_bool_sort());
    for (unsigned values = 0; values < static_cast<unsigned>(1 << N); ++values) {
        ref<solver> slv = mk_fd_solver(m, p);
        expr_ref_vector tf(m);
        for (unsigned i = 0; i < N; ++i) {
            bool is_true = 0 != (values & (1 << i));
            tf.push_back(is_true ? m.mk_true() : m.mk_false());
            slv->assert_expr(is_true ? vars[i] : m.mk_not(vars[i]));
        }
        slv->assert_expr(m.mk_eq(result1, fml1));
        
        switch (kind) {
        case 0: fml2 = pb.mk_ge(tf.size(), coeffs.c_ptr(), tf.c_ptr(), rational(k)); break;
        case 1: fml2 = pb.mk_le(tf.size(), coeffs.c_ptr(), tf.c_ptr(), rational(k)); break;
        default: fml2 = pb.mk_eq(tf.size(), coeffs.c_ptr(), tf.c_ptr(), rational(k)); break;
        }
        std::cout << fml1 << " " << fml2 << "\n";
        th_rw(fml2, result2, proof);
        ENSURE(m.is_true(result2) || m.is_false(result2));
        lbool res = slv->check_sat(0,nullptr);
        VERIFY(res == l_true);
        slv->assert_expr(m.is_true(result2) ? m.mk_not(result1) : result1.get());
        res = slv->check_sat(0,nullptr);
        VERIFY(res == l_false);
    }
}

static void test_solver_semantics(ast_manager& m, expr_ref_vector const& vars, vector<rational> const& coeffs, unsigned k) {
    test_solver_semantics(m, vars, coeffs, k, 0);
    test_solver_semantics(m, vars, coeffs, k, 1);
    test_solver_semantics(m, vars, coeffs, k, 2);
}

static void test3() {
    ast_manager m;
    reg_decl_plugins(m);
    expr_ref_vector vars(m);
    unsigned N = 4;
    for (unsigned i = 0; i < N; ++i) {
        std::stringstream strm;
        strm << "b" << i;
        vars.push_back(m.mk_const(symbol(strm.str().c_str()), m.mk_bool_sort()));
    }
    for (unsigned coeff = 0; coeff < static_cast<unsigned>(1 << N); ++coeff) {
        vector<rational> coeffs;
        for (unsigned i = 0; i < N; ++i) {
            bool is_one = 0 != (coeff & (1 << i));
            coeffs.push_back(is_one ? rational(1) : rational(2));
        }
        for (unsigned i = 0; i <= N; ++i) {
            test_solver_semantics(m, vars, coeffs, i);
        }
    }
}

void tst_pb2bv() {
    test1();
    test2();
    test3();
}

