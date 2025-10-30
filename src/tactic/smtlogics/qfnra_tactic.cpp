/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfnra_tactic.cpp

Abstract:

    Tactic for QF_NRA

Author:

    Leonardo (leonardo) 2012-02-28

Notes:

--*/
#include "tactic/tactical.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "tactic/arith/nla2bv_tactic.h"
#include "nlsat/tactic/qfnra_nlsat_tactic.h"
#include "tactic/smtlogics/smt_tactic.h"

#include "tactic/smtlogics/qflra_tactic.h"


tactic * mk_multilinear_ls_tactic(ast_manager & m, params_ref const & p, unsigned ls_time = 60) {
    params_ref p_mls = p;
    p_mls.set_bool("use_ls", true);
    p_mls.set_uint("ls_time",ls_time);
    return using_params(mk_smt_tactic(m), p_mls);
}

tactic * mk_qfnra_very_small_solver(ast_manager& m, params_ref const& p) {
    ptr_vector<tactic> ts;
    {
        params_ref p_sc = p;
        p_sc.set_bool("simple_check", true);
        // p_sc.set_uint("seed", 997);
        tactic* nlsat = mk_qfnra_nlsat_tactic(m, p_sc);
        tactic* fail_if_undecided = mk_fail_if_undecided_tactic();
        tactic* seq = and_then(nlsat, fail_if_undecided);
        tactic* limited = try_for(seq, 10 * 1000);
        ts.push_back(limited);
    }
    {
        params_ref p_heuristic = p;
        // p_heuristic.set_uint("seed", 233);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_heuristic), 4 * 1000));

        params_ref p_order_4 = p;
        p_order_4.set_uint("variable_ordering_strategy", 4);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_order_4), 4 * 1000));

        params_ref p_order_3 = p;
        p_order_3.set_uint("variable_ordering_strategy", 3);
        // p_order_3.set_uint("seed", 17);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_order_3), 6 * 1000));

        params_ref p_order_1 = p;
        p_order_1.set_uint("variable_ordering_strategy", 1);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_order_1), 8 * 1000));

        params_ref p_order_5 = p;
        p_order_5.set_uint("variable_ordering_strategy", 5);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_order_5), 8 * 1000));

        params_ref p_order_2 = p;
        p_order_2.set_uint("variable_ordering_strategy", 2);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_order_2), 10 * 1000));
    }
    {
        ts.push_back(mk_multilinear_ls_tactic(m, p, 60));
    }
    {
        params_ref p_l = p;
        p_l.set_bool("arith.greatest_error_pivot", true);
        tactic* smt = mk_smt_tactic(m);
        tactic* smt_with_params = using_params(smt, p_l);
        tactic* smt_limited = try_for(smt_with_params, 300 * 1000);
        tactic* fail_if_undecided = mk_fail_if_undecided_tactic();
        ts.push_back(and_then(smt_limited, fail_if_undecided));
    }
    for (unsigned i = 0; i < 200; ++i) { // 3s * 200 = 600s
        params_ref p_i = p;
        p_i.set_uint("seed", i);
        p_i.set_bool("shuffle_vars", true);
        // if ((i & 1) == 0)
        //     p_i.set_bool("randomize", false);
        ts.push_back(mk_lazy_tactic(m, p_i, [&](ast_manager& m, params_ref const& p) { return try_for(mk_qfnra_nlsat_tactic(m, p), 3 * 1000); }));
    }
    {
        ts.push_back(mk_qfnra_nlsat_tactic(m, p));
    }
    return or_else(ts.size(), ts.data());
}

tactic * mk_qfnra_small_solver(ast_manager& m, params_ref const& p) {
    ptr_vector<tactic> ts;
    {
        params_ref p_sc = p;
        p_sc.set_bool("simple_check", true);
        // p_sc.set_uint("seed", 997);
        tactic* nlsat = mk_qfnra_nlsat_tactic(m, p_sc);
        tactic* fail_if_undecided = mk_fail_if_undecided_tactic();
        tactic* seq = and_then(nlsat, fail_if_undecided);
        tactic* limited = try_for(seq, 20 * 1000);
        ts.push_back(limited);
    }
    {
        params_ref p_heuristic = p;
        // p_heuristic.set_uint("seed", 233);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_heuristic), 5 * 1000));

        params_ref p_order_4 = p;
        p_order_4.set_uint("variable_ordering_strategy", 4);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_order_4), 5 * 1000));

        params_ref p_order_3 = p;
        p_order_3.set_uint("variable_ordering_strategy", 3);
        // p_order_3.set_uint("seed", 17);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_order_3), 10 * 1000));

        params_ref p_order_1 = p;
        p_order_1.set_uint("variable_ordering_strategy", 1);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_order_1), 15 * 1000));

        
        params_ref p_order_5 = p;
        p_order_5.set_uint("variable_ordering_strategy", 5);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_order_5), 15 * 1000));
        

        params_ref p_order_2 = p;
        p_order_2.set_uint("variable_ordering_strategy", 2);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_order_2), 20 * 1000));
    }
    {
        ts.push_back(mk_multilinear_ls_tactic(m, p, 70));
    }
    {
        params_ref p_l = p;
        p_l.set_bool("arith.greatest_error_pivot", true);
        tactic* smt = mk_smt_tactic(m);
        tactic* smt_with_params = using_params(smt, p_l);
        tactic* smt_limited = try_for(smt_with_params, 350 * 1000);
        tactic* fail_if_undecided = mk_fail_if_undecided_tactic();
        ts.push_back(and_then(smt_limited, fail_if_undecided));
    }
    for (unsigned i = 0; i < 100; ++i) { // 5s * 100 = 500s
        params_ref p_i = p;
        p_i.set_uint("seed", i);
        p_i.set_bool("shuffle_vars", true);
        // if ((i & 1) == 0)
        //     p_i.set_bool("randomize", false);
        ts.push_back(mk_lazy_tactic(m, p_i, [&](ast_manager& m, params_ref const& p) { return try_for(mk_qfnra_nlsat_tactic(m, p), 5 * 1000); }));
    }
    {
        ts.push_back(mk_qfnra_nlsat_tactic(m, p));
    }
    return or_else(ts.size(), ts.data());
}

tactic * mk_qfnra_middle_solver(ast_manager& m, params_ref const& p) {
    ptr_vector<tactic> ts;
    {
        params_ref p_sc = p;
        p_sc.set_bool("simple_check", true);
        tactic* nlsat = mk_qfnra_nlsat_tactic(m, p_sc);
        tactic* fail_if_undecided = mk_fail_if_undecided_tactic();
        tactic* seq = and_then(nlsat, fail_if_undecided);
        tactic* limited = try_for(seq, 30 * 1000);
        ts.push_back(limited);
    }
    {
        params_ref p_heuristic = p;
        // p_heuristic.set_uint("seed", 233);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_heuristic), 10 * 1000));

        
        params_ref p_order_4 = p;
        p_order_4.set_uint("variable_ordering_strategy", 4);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_order_4), 15 * 1000));
        

        params_ref p_order_3 = p;
        p_order_3.set_uint("variable_ordering_strategy", 3);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_order_3), 15 * 1000));

        params_ref p_order_1 = p;
        p_order_1.set_uint("variable_ordering_strategy", 1);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_order_1), 20 * 1000));

        
        params_ref p_order_5 = p;
        p_order_5.set_uint("variable_ordering_strategy", 5);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_order_5), 20 * 1000));
        

        params_ref p_order_2 = p;
        p_order_2.set_uint("variable_ordering_strategy", 2);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_order_2), 25 * 1000));
    }
    {
        ts.push_back(mk_multilinear_ls_tactic(m, p, 80));
    }
    {
        params_ref p_l = p;
        p_l.set_bool("arith.greatest_error_pivot", true);
        tactic* smt = mk_smt_tactic(m);
        tactic* smt_with_params = using_params(smt, p_l);
        tactic* smt_limited = try_for(smt_with_params, 375 * 1000);
        tactic* fail_if_undecided = mk_fail_if_undecided_tactic();
        ts.push_back(and_then(smt_limited, fail_if_undecided));
    }
    for (unsigned i = 0; i < 40; ++i) { // 10s * 40 = 400s
        params_ref p_i = p;
        p_i.set_uint("seed", i);
        p_i.set_bool("shuffle_vars", true);
        // if ((i & 1) == 0)
        //     p_i.set_bool("randomize", false);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_i), 10 * 1000));
    }
    {
        ts.push_back(mk_qfnra_nlsat_tactic(m, p));
    }
    return or_else(ts.size(), ts.data());
}

tactic * mk_qfnra_large_solver(ast_manager& m, params_ref const& p) {
    ptr_vector<tactic> ts;
    {
        params_ref p_sc = p;
        p_sc.set_bool("simple_check", true);
        tactic* nlsat = mk_qfnra_nlsat_tactic(m, p_sc);
        tactic* fail_if_undecided = mk_fail_if_undecided_tactic();
        tactic* seq = and_then(nlsat, fail_if_undecided);
        tactic* limited = try_for(seq, 50 * 1000);
        ts.push_back(limited);
    }
    {

        params_ref p_order_4 = p;
        p_order_4.set_uint("variable_ordering_strategy", 4);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_order_4), 15 * 1000));
        

        params_ref p_order_3 = p;
        p_order_3.set_uint("variable_ordering_strategy", 3);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_order_3), 30 * 1000));

        params_ref p_order_1 = p;
        p_order_1.set_uint("variable_ordering_strategy", 1);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_order_1), 40 * 1000));

        
        params_ref p_order_5 = p;
        p_order_5.set_uint("variable_ordering_strategy", 5);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_order_5), 40 * 1000));
        

        params_ref p_order_2 = p;
        p_order_2.set_uint("variable_ordering_strategy", 2);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_order_2), 50 * 1000));
    }
    {
        ts.push_back(mk_multilinear_ls_tactic(m, p, 90));
    }
    {
        params_ref p_l = p;
        p_l.set_bool("arith.greatest_error_pivot", true);
        tactic* smt = mk_smt_tactic(m);
        tactic* smt_with_params = using_params(smt, p_l);
        tactic* smt_limited = try_for(smt_with_params, 400 * 1000);
        tactic* fail_if_undecided = mk_fail_if_undecided_tactic();
        ts.push_back(and_then(smt_limited, fail_if_undecided));
    }
    for (unsigned i = 0; i < 10; ++i) { // 20s * 10 = 200s
        params_ref p_i = p;
        p_i.set_uint("seed", i);
        p_i.set_bool("shuffle_vars", true);
        // if ((i & 1) == 0)
        //     p_i.set_bool("randomize", false);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_i), 20 * 1000));
    }
    {
        ts.push_back(mk_qfnra_nlsat_tactic(m, p));
    }
    return or_else(ts.size(), ts.data());
}

tactic * mk_qfnra_very_large_solver(ast_manager& m, params_ref const& p) {
    ptr_vector<tactic> ts;
    {
        params_ref p_sc = p;
        p_sc.set_bool("simple_check", true);
        tactic* nlsat = mk_qfnra_nlsat_tactic(m, p_sc);
        tactic* fail_if_undecided = mk_fail_if_undecided_tactic();
        tactic* seq = and_then(nlsat, fail_if_undecided);
        tactic* limited = try_for(seq, 100 * 1000);
        ts.push_back(limited);
    }
    {
        params_ref p_order_1 = p;
        p_order_1.set_uint("variable_ordering_strategy", 1);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_order_1), 80 * 1000));

        
        params_ref p_order_5 = p;
        p_order_5.set_uint("variable_ordering_strategy", 5);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_order_5), 80 * 1000));
        

        params_ref p_order_2 = p;
        p_order_2.set_uint("variable_ordering_strategy", 2);
        ts.push_back(try_for(mk_qfnra_nlsat_tactic(m, p_order_2), 100 * 1000));
    }
    {
        ts.push_back(mk_multilinear_ls_tactic(m, p, 100));
    }
    {
        params_ref p_l = p;
        p_l.set_bool("arith.greatest_error_pivot", true);
        tactic* smt = mk_smt_tactic(m);
        tactic* smt_with_params = using_params(smt, p_l);
        tactic* smt_limited = try_for(smt_with_params, 425 * 1000);
        tactic* fail_if_undecided = mk_fail_if_undecided_tactic();
        ts.push_back(and_then(smt_limited, fail_if_undecided));
    }
    {
        ts.push_back(mk_qfnra_nlsat_tactic(m, p));
    }
    return or_else(ts.size(), ts.data());
}

const double VERY_SMALL_THRESHOLD = 30.0;
const double SMALL_THRESHOLD = 80.0;
const double MIDDLE_THRESHOLD = 300.0;
const double LARGE_THRESHOLD = 600.0;
tactic * mk_qfnra_mixed_solver(ast_manager& m, params_ref const& p) {
    auto very_small_t = mk_lazy_tactic(m, p, [&](ast_manager& m, params_ref const& p) {return mk_qfnra_very_small_solver(m, p); });
    auto small_t = mk_lazy_tactic(m, p, [&](ast_manager& m, params_ref const& p) {return mk_qfnra_small_solver(m, p); });
   auto middle_t = mk_lazy_tactic(m, p, [&](ast_manager& m, params_ref const& p) {return mk_qfnra_middle_solver(m, p); });
   auto large_t = mk_lazy_tactic(m, p, [&](ast_manager& m, params_ref const& p) {return mk_qfnra_large_solver(m, p); });
   auto very_large_t = mk_lazy_tactic(m, p, [&](ast_manager& m, params_ref const& p) {return mk_qfnra_very_large_solver(m, p); });
    probe* memory_usage = mk_memory_probe();
    probe* very_small_limit = mk_const_probe(VERY_SMALL_THRESHOLD);
    probe* small_limit = mk_const_probe(SMALL_THRESHOLD);
    probe* middle_limit = mk_const_probe(MIDDLE_THRESHOLD);
    probe* large_limit = mk_const_probe(LARGE_THRESHOLD);

    probe* very_small_check = mk_lt(memory_usage, very_small_limit);
    probe* small_check = mk_lt(memory_usage, small_limit);
    probe* middle_check = mk_lt(memory_usage, middle_limit);
    probe* large_check = mk_lt(memory_usage, large_limit);

    tactic* large_branch = cond(large_check, large_t, very_large_t);
    tactic* middle_branch = cond(middle_check, middle_t, large_branch);
    tactic* small_branch = cond(small_check, small_t, middle_branch);
    return cond(very_small_check, very_small_t, small_branch);
}

tactic * mk_qfnra_tactic(ast_manager & m, params_ref const& p) {

    tactic* simplify = mk_simplify_tactic(m, p);
    tactic* propagate = mk_propagate_values_tactic(m, p);
    tactic* mixed_solver = mk_qfnra_mixed_solver(m, p);

    return and_then(simplify, 
                    propagate,
                    mixed_solver
                );
}
