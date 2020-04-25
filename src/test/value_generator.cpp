#include "ast/value_generator.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_pp.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "ast/array_decl_plugin.h"

static void list(unsigned bound, ast_manager& m, sort* s) {
    value_generator gen(m);
    for (unsigned i = 0; i < bound; ++i) {
        std::cout << gen.get_value(s, i) << "\n";
    }
}

static void tst1_vg() {
    ast_manager m;
    reg_decl_plugins(m);
    datatype_util dt(m);
    arith_util a(m);
    array_util ar(m);
    seq_util seq(m);
    sort_ref int_sort(a.mk_int(), m);
    func_decl_ref cons(m), is_cons(m), head(m), tail(m), nil(m), is_nil(m);

    sort_ref bool_seq(seq.str.mk_seq(m.mk_bool_sort()), m);
    list(16, m, bool_seq);
    return;

    sort_ref ilist = dt.mk_list_datatype(int_sort, symbol("ilist"), 
                                     cons, is_cons, head, tail, nil, is_nil);
    list(100, m, ilist);

    sort_ref blist = dt.mk_list_datatype(m.mk_bool_sort(), symbol("blist"), 
                                     cons, is_cons, head, tail, nil, is_nil);
    list(100, m, blist);
    
    sort_ref rlist = dt.mk_list_datatype(a.mk_real(), symbol("rlist"), 
                                     cons, is_cons, head, tail, nil, is_nil);
    list(100, m, rlist);

    list(100, m, a.mk_real());
    list(100, m, a.mk_int());

    sort_ref int_seq(seq.str.mk_seq(a.mk_int()), m);
    list(100, m, int_seq);

    sort_ref as(m);
    as = ar.mk_array_sort(a.mk_int(), a.mk_int());
    list(100, m, as);
    as = ar.mk_array_sort(m.mk_bool_sort(), a.mk_int());
    list(100, m, as);
    as = ar.mk_array_sort(m.mk_bool_sort(), m.mk_bool_sort());
    list(10, m, as);

}

void tst_value_generator() {
    tst1_vg();
}
