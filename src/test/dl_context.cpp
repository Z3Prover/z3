
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "muz/fp/datalog_parser.h"
#include "ast/ast_pp.h"
#include "ast/arith_decl_plugin.h"
#include "muz/base/dl_context.h"
#include "smt/params/smt_params.h"
#include "muz/fp/dl_register_engine.h"

using namespace datalog;


void tst_dl_context() {

    return;

#if 0
    symbol relations[] = { symbol("tr_skip"), symbol("tr_sparse"), symbol("tr_hashtable"), symbol("smt_relation2")  };

    const unsigned rel_cnt = sizeof(relations)/sizeof(symbol);
    const char * test_file = "c:\\tvm\\src\\benchmarks\\datalog\\t0.datalog";

    params_ref params;
    for(unsigned rel_index=0; rel_index<rel_cnt; rel_index++) {
        params.set_sym("default_relation", relations[rel_index]);
        for(int eager_checking=1; eager_checking>=0; eager_checking--) {
            params.set_bool("eager_emptiness_checking", eager_checking!=0);

            std::cerr << "Testing " << relations[rel_index] << "\n";
            std::cerr << "Eager emptiness checking " << (eager_checking!=0 ? "on" : "off") << "\n";
            dl_context_simple_query_test(params);
            dl_context_saturate_file(params, test_file);
        }
    }
#endif

}


#if 0


static lbool dl_context_eval_unary_predicate(ast_manager & m, context & ctx, char const* problem_text, 
        const char * pred_name) {
    parser* p = parser::create(ctx,m);
    TRUSTME( p->parse_string(problem_text) );
    dealloc(p);

    func_decl * pred = ctx.try_get_predicate_decl(symbol(pred_name));
    ENSURE(pred);
    ENSURE(pred->get_arity()==1);
    app_ref query_app(m.mk_app(pred, m.mk_var(0, pred->get_domain()[0])), m);

    lbool status = ctx.query(query_app);
    ENSURE(status != l_undef);
    return status;
}

static void dl_context_simple_query_test(params_ref & params) {
    ast_manager m;
    dl_decl_util decl_util(m);
    register_engine re;
    smt_params fparams;
    context ctx(m, re, fparams);
    ctx.updt_params(params);

    /* lbool status = */ dl_context_eval_unary_predicate(m, ctx, "Z 64\n\nP(x:Z)\nP(\"a\").", "P");

#if 0
    // TBD:
    //zero corresponds to the first constant the datalog parser encountered, in our case "a"
    app_ref c_0(decl_util.mk_constant(0, res1->get_signature()[0]), m);
    app_ref c_1(decl_util.mk_constant(1, res1->get_signature()[0]), m);
    relation_fact f(m);
    f.push_back(c_0);
    ENSURE(res1->contains_fact(f));
    f[0]=c_1;
    ENSURE(!res1->contains_fact(f));
#endif
}

void dl_context_saturate_file(params_ref & params, const char * f) {
    ast_manager m;
    dl_decl_util decl_util(m);
    smt_params fparams;
    register_engine re;
    context ctx(m, re, fparams);
    ctx.updt_params(params);

    datalog::parser * parser = datalog::parser::create(ctx, m);
    if (!parser || !parser->parse_file(f)) {
        warning_msg("ERROR: failed to parse file");
        dealloc(parser);
        return;
    }
    dealloc(parser);
    std::cerr << "Saturating...\n";
    ctx.get_rel_context()->saturate();
    std::cerr << "Done\n";
}
#endif
