/*++
Copyright (c) 2015 Microsoft Corporation
--*/
#if defined(_WINDOWS) || defined(_CYGWIN)

#include "muz/base/dl_context.h"
#include "muz/rel/dl_table.h"
#include "muz/fp/dl_register_engine.h"
#include "muz/rel/dl_relation_manager.h"

typedef datalog::table_base* (*mk_table_fn)(datalog::relation_manager& m, datalog::table_signature& sig);

static datalog::table_base* mk_bv_table(datalog::relation_manager& m, datalog::table_signature& sig) {
    datalog::table_plugin * p = m.get_table_plugin(symbol("bitvector"));
    ENSURE(p);
    return p->mk_empty(sig);
}

static void test_table(mk_table_fn mk_table) {
    datalog::table_signature sig;
    sig.push_back(2);
    sig.push_back(4);
    sig.push_back(8);
    sig.push_back(4);
    smt_params params;
    ast_manager ast_m;
    datalog::register_engine re;
    datalog::context ctx(ast_m, re, params);    
    datalog::relation_manager & m = ctx.get_rel_context()->get_rmanager();

    m.register_plugin(alloc(datalog::bitvector_table_plugin, m));

    datalog::table_base* _tbl = mk_table(m, sig);
    datalog::table_base& table = *_tbl;
    datalog::table_fact row, row1, row2, row3;
    row.push_back(1);
    row.push_back(3);
    row.push_back(7);
    row.push_back(2);
    row1 = row;
    row[3] = 3;
    row2 = row;
    row[0] = 0;
    row[3] = 1;
    row3 = row;
    table.add_fact(row1);
    table.add_fact(row2);
    table.display(std::cout);

    datalog::table_base::iterator it = table.begin();
    datalog::table_base::iterator end = table.end();
    for (; it != end; ++it) {
        it->get_fact(row);
        for (unsigned j = 0; j < row.size(); ++j) {
            std::cout << row[j] << " ";
        }
        std::cout << "\n";
    }

    ENSURE(table.contains_fact(row1));
    ENSURE(table.contains_fact(row2));
    ENSURE(!table.contains_fact(row3));
#if 0
    table.remove_facts(1, &row1);
    ENSURE(!table.contains_fact(row1));
#endif
    table.add_fact(row1);

    datalog::table_base* _tbl2 = mk_table(m, sig);
    datalog::table_base& table2 = *_tbl2;
    table2.add_fact(row2);
    table2.add_fact(row3);

    unsigned cols1[1] = { 1 };
    unsigned cols2[1] = { 3 };

    datalog::table_join_fn * j1 = m.mk_join_fn(table2, table, 1, cols1, cols2);
    datalog::table_base* _tbl3 = (*j1)(table2,table);
    _tbl3->display(std::cout);

    datalog::table_join_fn * j2 = m.mk_join_fn(table2, table, 1, cols1, cols1);
    datalog::table_base* _tbl4 = (*j2)(table2,table);
    _tbl4->display(std::cout);

    dealloc(j1);
    dealloc(j2);
    _tbl->deallocate();
    (_tbl2->deallocate());
    (_tbl3->deallocate());
    (_tbl4->deallocate());

}

void test_dl_bitvector_table() {
    test_table(mk_bv_table);
}

void tst_dl_table() {
    test_dl_bitvector_table();
}
#else
void tst_dl_table() {
}
#endif
