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
        ts.push_back(try_for(and_then(mk_qfnra_nlsat_tactic(m, p_sc), mk_fail_if_undecided_tactic()), 10 * 1000));
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
        ts.push_back(and_then(try_for(using_params(mk_smt_tactic(m), p_l), 300 * 1000), mk_fail_if_undecided_tactic()));
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
        ts.push_back(try_for(and_then(mk_qfnra_nlsat_tactic(m, p_sc), mk_fail_if_undecided_tactic()), 20 * 1000));
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
        ts.push_back(and_then(try_for(using_params(mk_smt_tactic(m), p_l), 350 * 1000), mk_fail_if_undecided_tactic()));
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
        ts.push_back(try_for(and_then(mk_qfnra_nlsat_tactic(m, p_sc), mk_fail_if_undecided_tactic()), 30 * 1000));
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
        ts.push_back(and_then(try_for(using_params(mk_smt_tactic(m), p_l), 375 * 1000), mk_fail_if_undecided_tactic()));
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
        ts.push_back(try_for(and_then(mk_qfnra_nlsat_tactic(m, p_sc), mk_fail_if_undecided_tactic()), 50 * 1000));
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
        ts.push_back(and_then(try_for(using_params(mk_smt_tactic(m), p_l), 400 * 1000), mk_fail_if_undecided_tactic()));
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
        ts.push_back(try_for(and_then(mk_qfnra_nlsat_tactic(m, p_sc), mk_fail_if_undecided_tactic()), 100 * 1000));
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
        ts.push_back(and_then(try_for(using_params(mk_smt_tactic(m), p_l), 425 * 1000), mk_fail_if_undecided_tactic()));
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
    return cond(mk_lt(mk_memory_probe(), mk_const_probe(VERY_SMALL_THRESHOLD)), 
        very_small_t,
                cond(mk_lt(mk_memory_probe(), mk_const_probe(SMALL_THRESHOLD)), 
                    small_t,
                     cond(mk_lt(mk_memory_probe(), mk_const_probe(MIDDLE_THRESHOLD)),
                         middle_t,
                          cond(mk_lt(mk_memory_probe(), mk_const_probe(LARGE_THRESHOLD)),
                             large_t,
                             very_large_t
                        )
                    )
                )
           );
}

tactic * mk_qfnra_tactic(ast_manager & m, params_ref const& p) {

    return and_then(mk_simplify_tactic(m, p), 
                    mk_propagate_values_tactic(m, p),
                    mk_qfnra_mixed_solver(m, p)
                );
}
