#include "ast/rewriter/value_sweep.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_pp.h"
#include "ast/seq_decl_plugin.h"
#include "ast/array_decl_plugin.h"

void tst_value_sweep() {
    ast_manager m;
    reg_decl_plugins(m);
    datatype_util dt(m);
    arith_util a(m);
    array_util ar(m);
    seq_util seq(m);
    sort_ref int_sort(a.mk_int(), m);
    func_decl_ref cons(m), is_cons(m), head(m), tail(m), nil(m), is_nil(m);

    sort_ref ilist = dt.mk_list_datatype(int_sort, symbol("ilist"), 
                                     cons, is_cons, head, tail, nil, is_nil);

    expr_ref n(m.mk_const("n", int_sort), m);
    expr_ref v1(m.mk_const("v1", ilist), m);
    expr_ref v2(m.mk_const("v2", ilist), m);
    std::cout << cons << "\n";
    expr_ref v3(m.mk_app(cons.get(), n, v1), m);
    expr_ref_vector terms(m);
    terms.push_back(v1).push_back(v2).push_back(v3);
    vector<expr_ref_vector> values;
    value_sweep ws(m);
    ws.set_range(30);
    ws(terms, values);
    for (auto const& vec : values) {
        for (expr* v : vec) {
            std::cout << mk_pp(v, m) << "\n";
        }
        std::cout << "\n";
    }
}
