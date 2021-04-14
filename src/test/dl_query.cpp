
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "muz/fp/datalog_parser.h"
#include "ast/ast_pp.h"
#include "muz/rel/dl_table_relation.h"
#include "muz/base/dl_context.h"
#include "muz/fp/dl_register_engine.h"
#include "smt/params/smt_params.h"
#include "util/stopwatch.h"
#include "ast/reg_decl_plugins.h"
#include "muz/rel/dl_relation_manager.h"

using namespace datalog;

void dl_query_ask_ground_query(context & ctx, func_decl * pred, relation_fact & f, bool should_be_successful) {
    expr * const * q_args = reinterpret_cast<expr * const *>(f.data());
    app * query = ctx.get_manager().mk_app(pred, q_args);

    lbool is_sat = ctx.query(query);
    
    std::cerr << "@@ query should succeed: " << should_be_successful << "\n";
    ENSURE(is_sat != l_undef);
    if((is_sat != l_true) == should_be_successful) {
        std::cerr<<"wrong ground query answer!\n";
        UNREACHABLE();
    }
}

void dl_query_ask_for_last_arg(context & ctx, func_decl * pred, relation_fact & f, bool should_be_successful) {
    ast_manager & m = ctx.get_manager();
    expr_ref_vector query_args(m);
    push_into_vector(query_args, f);
    query_args.pop_back();
    query_args.push_back(m.mk_var(0, pred->get_domain(query_args.size())));
    app * query = ctx.get_manager().mk_app(pred, query_args.data());

    lbool is_sat = ctx.query(query);
    std::cerr << "@@ last arg query should succeed: " << should_be_successful << "\n";
    VERIFY(is_sat != l_undef);

    relation_fact res_fact(m);
    res_fact.push_back(f.back());

    if(ctx.result_contains_fact(res_fact)!=should_be_successful) {
        std::cerr<<"wrong arg query answer!\n";
        UNREACHABLE();
    }
}

void dl_query_test(ast_manager & m, smt_params & fparams, params_ref& params,
        context & ctx_b, char const* problem_file, unsigned test_count,
        bool use_magic_sets) {

    dl_decl_util decl_util(m);
    random_gen ran(0);

    register_engine re;
    context ctx_q(m, re, fparams);
    params.set_bool("magic_sets_for_queries", use_magic_sets);
    ctx_q.updt_params(params);
    {
        parser* p = parser::create(ctx_q,m);
        bool ok = p && p->parse_file(problem_file);
        dealloc(p);
        if (!ok) {
            std::cout << "Could not parse: " << problem_file << "\n";
            return;
        }
    }
    relation_manager & rel_mgr_q = ctx_b.get_rel_context()->get_rmanager();

    decl_set out_preds = ctx_b.get_rules().get_output_predicates();
    decl_set::iterator it = out_preds.begin();
    decl_set::iterator end = out_preds.end();
    for(; it!=end; ++it) {
        func_decl * pred_b = *it;
        std::cerr << "Checking queries on relation " << pred_b->get_name() << "\n";
        func_decl * pred_q = ctx_q.try_get_predicate_decl(symbol(pred_b->get_name().bare_str()));
        ENSURE(pred_q);

        relation_base & rel_b = ctx_b.get_rel_context()->get_relation(pred_b);

        relation_signature sig_b = rel_b.get_signature();
        relation_signature sig_q = ctx_q.get_rel_context()->get_relation(pred_q).get_signature();
        ENSURE(sig_b.size()==sig_q.size());

        std::cerr << "Queries on random facts...\n";
        relation_fact f_b(m);
        relation_fact f_q(m);
        for(unsigned attempt=0; attempt<test_count; attempt++) {
            f_b.reset();
            f_q.reset();
            for(unsigned col=0; col<sig_b.size(); col++) {
                uint64_t sort_sz;
                if(!decl_util.try_get_size(sig_q[col], sort_sz)) {
                    warning_msg("cannot get sort size");
                    return;
                }
                uint64_t num = ran()%sort_sz;
                app * el_b = decl_util.mk_numeral(num, sig_b[col]);
                f_b.push_back(el_b);
                app * el_q = decl_util.mk_numeral(num, sig_q[col]);
                f_q.push_back(el_q);
            }

            bool found_in_b = rel_b.contains_fact(f_b);

            dl_query_ask_ground_query(ctx_q, pred_q, f_q, found_in_b);
            dl_query_ask_for_last_arg(ctx_q, pred_q, f_q, found_in_b);
        }

        std::cerr << "Queries on table facts...\n";
        if(!rel_b.from_table()) {
            warning_msg("relation is not a table_relation, skipping queries on facts");
        }
        table_relation & tr_b = static_cast<table_relation &>(rel_b);
        table_base & table_b = tr_b.get_table();

        table_fact tf;
        unsigned table_sz = table_b.get_size_estimate_rows();

        table_base::iterator fit = table_b.begin();
        table_base::iterator fend = table_b.end();
        for(; fit!=fend; ++fit) {
            if(ran()%std::max(1u,table_sz/test_count)!=0) {
                continue;
            }
            fit->get_fact(tf);
            rel_mgr_q.table_fact_to_relation(sig_q, tf, f_q);
            dl_query_ask_ground_query(ctx_q, pred_q, f_q, true);
            dl_query_ask_for_last_arg(ctx_q, pred_q, f_q, true);
        }
        std::cerr << "Done.\n";
    }
}

void dl_query_test_wpa(smt_params & fparams, params_ref& params) {
    params.set_bool("magic_sets_for_queries", true);
    ast_manager m;
    random_gen ran(0);
    reg_decl_plugins(m);
    arith_util arith(m);
    const char * problem_dir = "C:\\tvm\\src\\z3_2\\debug\\test\\w0.datalog";
    dl_decl_util dl_util(m);

    std::cerr << "Testing queries on " << problem_dir <<"\n";
    register_engine re;
    context ctx(m, re, fparams);
    ctx.updt_params(params);
    {
        wpa_parser* p = wpa_parser::create(ctx, m);
        bool ok = p->parse_directory(problem_dir);
        dealloc(p);
        if (!ok) {
            std::cout << "Could not parse: " << problem_dir << "\n";
            return;
        }
    }

    const unsigned attempts = 10;

    func_decl * v_pred = ctx.try_get_predicate_decl(symbol("V"));
    ENSURE(v_pred);
    sort * var_sort = v_pred->get_domain(0);

    uint64_t var_sz;
    TRUSTME( ctx.try_get_sort_constant_count(var_sort, var_sz) );

    for(unsigned attempt=0; attempt<attempts; attempt++) {
        unsigned el1 = ran()%var_sz;
        unsigned el2 = ran()%var_sz;
        
        expr_ref_vector q_args(m);
        q_args.push_back(dl_util.mk_numeral(el1, var_sort));
        q_args.push_back(dl_util.mk_numeral(el2, var_sort));

        app_ref query_lit(m.mk_app(v_pred, q_args.data()), m);
        lbool is_sat = ctx.query(query_lit);
        ENSURE(is_sat != l_undef);
        bool found = is_sat == l_true;
        std::cerr<<"query finished: "<<found<<"\n";

        relation_fact ans_fact(m);
        ans_fact.push_back(to_app(q_args.back()));

        q_args.pop_back();
        q_args.push_back(m.mk_var(0, var_sort));

        query_lit = m.mk_app(v_pred, q_args.data());
        is_sat = ctx.query(query_lit.get());
        ENSURE(is_sat != l_false);
        std::cerr<<"non-ground query finished\n";
        if(ctx.result_contains_fact(ans_fact)!=found) {
            std::cerr<<"wrong wpa answer!\n";
            UNREACHABLE();
        }
    }

}

void tst_dl_query() {
    smt_params fparams;
    params_ref params;
    params.set_sym("default_table", symbol("sparse"));
    params.set_sym("default_relation", symbol("tr_sparse"));

    //params.m_dl_default_table = symbol("hashtable");
    //params.m_dl_default_relation = symbol("tr_hashtable");

    //dl_query_test_wpa(params);
    return;


    ast_manager m;
    //const char * problem_file = "C:\\tvm\\src\\z3_2\\debug\\test\\test1.datalog";
    //const char * problem_file = "C:\\tvm\\src\\benchmarks\\datalog\\test.datalog";
    const char * problem_file = "C:\\tvm\\src\\benchmarks\\datalog\\t0.datalog";
    //const char * problem_file = "C:\\tvm\\src\\benchmarks\\datalog\\p0.datalog";

    std::cerr << "Testing queries on " << problem_file <<"\n";

    register_engine re;
    context ctx_base(m, re, fparams);
    ctx_base.updt_params(params);
    {
        parser* p = parser::create(ctx_base,m);
        bool ok = p->parse_file(problem_file);
        dealloc(p);
        if (!ok) {
            std::cout << "Could not parse: " << problem_file << "\n";
            return;
        }
    }
    ctx_base.get_rel_context()->saturate();

    for(unsigned use_restarts=0; use_restarts<=1; use_restarts++) {
        params.set_uint("initial_restart_timeout", use_restarts ? 100 : 0);
        for(unsigned use_similar=0; use_similar<=1; use_similar++) {
            params.set_uint("similarity_compressor", use_similar != 0);

            for(unsigned use_magic_sets=0; use_magic_sets<=1; use_magic_sets++) {
                stopwatch watch;
                if (!(use_restarts == 1 && use_similar == 0 && use_magic_sets == 1)) {
                    continue;
                }
                watch.start();
                std::cerr << "------- " << (use_restarts ? "With" : "Without") << " restarts -------\n";
                std::cerr << "------- " << (use_similar ? "With" : "Without") << " similar compressor -------\n";
                std::cerr << "------- " << (use_magic_sets ? "With" : "Without") << " magic sets -------\n";
                dl_query_test(m, fparams, params, ctx_base, problem_file, 1, use_magic_sets!=0);
                watch.stop();
                std::cout << (use_restarts ? "With" : "Without") << " restarts\n";
                std::cout << (use_similar ? "With" : "Without") << " similar compressor\n";
                std::cout << (use_magic_sets ? "With" : "Without") << " magic sets\n";
                std::cout << "Time: " << watch.get_current_seconds() << "\n\n";
                std::cerr << "Time: " << watch.get_current_seconds() << "\n";

            }
        }
    }
}



