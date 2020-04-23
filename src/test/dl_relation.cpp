
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#ifdef _WINDOWS

#include "ast/reg_decl_plugins.h"
#include "muz/base/dl_context.h"
#include "muz/fp/dl_register_engine.h"
#include "muz/rel/dl_relation_manager.h"
#include "muz/rel/dl_interval_relation.h"
#include "muz/rel/dl_bound_relation.h"
#include "muz/rel/dl_product_relation.h"
#include "util/util.h"

namespace datalog {

    static void test_interval_relation() {
        smt_params params;
        ast_manager ast_m;
        reg_decl_plugins(ast_m);
        register_engine re;
        context ctx(ast_m, re, params);    
        arith_util autil(ast_m);
        relation_manager & m = ctx.get_rel_context()->get_rmanager();
        m.register_plugin(alloc(interval_relation_plugin, m));
        interval_relation_plugin& ip = dynamic_cast<interval_relation_plugin&>(*m.get_relation_plugin(symbol("interval_relation")));
        ENSURE(&ip);
        
        relation_signature sig;
        sort* int_sort = autil.mk_int();
        sig.push_back(int_sort);
        sig.push_back(int_sort);
        sig.push_back(int_sort);
        sig.push_back(int_sort);

        interval_relation& i1 = dynamic_cast<interval_relation&>(*ip.mk_empty(sig));
        interval_relation& i2 = dynamic_cast<interval_relation&>(*ip.mk_full(0, sig));

        i1.display(std::cout);
        i2.display(std::cout);
        ENSURE(i1.empty());
        ENSURE(!i2.empty());

        app_ref cond1(ast_m), cond2(ast_m), cond3(ast_m);
        app_ref cond4(ast_m), cond5(ast_m), cond6(ast_m);
        app_ref num1(ast_m);
        cond1 = autil.mk_le(ast_m.mk_var(0, int_sort), autil.mk_numeral(rational(0), true));
        cond2 = autil.mk_le(ast_m.mk_var(1, int_sort), autil.mk_numeral(rational(1), true));
        cond3 = autil.mk_le(ast_m.mk_var(2, int_sort), autil.mk_numeral(rational(2), true));
        cond4 = autil.mk_ge(ast_m.mk_var(0, int_sort), autil.mk_numeral(rational(0), true));
        cond5 = autil.mk_ge(ast_m.mk_var(1, int_sort), autil.mk_numeral(rational(0), true));
        cond6 = autil.mk_ge(ast_m.mk_var(2, int_sort), autil.mk_numeral(rational(5), true));
        num1 = autil.mk_numeral(rational(4), true);
        i2.filter_interpreted(cond1);
        i2.display(std::cout);
        // x0 <= 0
        
        unsigned cols1[2] = { 1, 2};
        unsigned cols2[2] = { 2, 3};
        relation_join_fn* join1 = ip.mk_join_fn(i1, i2, 2, cols1, cols2);        
        relation_transformer_fn* proj1 = ip.mk_project_fn(i1, 2, cols2);
        relation_transformer_fn* ren1  = ip.mk_rename_fn(i1, 2, cols2);
        relation_union_fn*       union1 = ip.mk_union_fn(i1, i2, &i1);
        relation_mutator_fn*     filterId1 = ip.mk_filter_identical_fn(i1, 2, cols1);
        relation_mutator_fn*     filterEq1 = ip.mk_filter_equal_fn(i1, num1, 2);               
        relation_mutator_fn*     filterCond1 = ip.mk_filter_interpreted_fn(i1, cond2);

        relation_base* i3 = (*join1)(i2, i2);
        i3->display(std::cout);       
 
        relation_transformer_fn* proj2 = ip.mk_project_fn(*i3, 2, cols2);

        (*filterEq1)(i2);
        i2.display(std::cout);
        // x0 <= 0
        // x2 = 4

        (*filterId1)(i2);
        i2.display(std::cout);
        // x0 <= 0
        // x1 = x2 = 4       
        relation_fact fact1(ast_m);
        fact1.push_back(autil.mk_numeral(rational(0), true));
        fact1.push_back(autil.mk_numeral(rational(4), true));
        fact1.push_back(autil.mk_numeral(rational(4), true));
        fact1.push_back(autil.mk_numeral(rational(5), true));
        ENSURE(i2.contains_fact(fact1));
        fact1[0] = autil.mk_numeral(rational(-1), true);
        ENSURE(i2.contains_fact(fact1));
        fact1[0] = autil.mk_numeral(rational(1), true);
        ENSURE(!i2.contains_fact(fact1));

        relation_base* i5 = (*ren1)(i2);
        i2.display(std::cout << "Orig\n");
        i5->display(std::cout << "renamed 2 |-> 3 |-> 2\n");

        (*filterCond1)(i2);
        i2.display(std::cout);
        // empty
        ENSURE(i2.empty());

        relation_base* i4 = (*proj2)(*i3);
        i4->display(std::cout);      
        
        i1.deallocate();
        i2.deallocate();
        i3->deallocate();
        i4->deallocate();
        i5->deallocate();
        dealloc(join1);
        dealloc(proj1);
        dealloc(ren1);
        dealloc(union1);
        dealloc(filterId1);
        dealloc(filterEq1);
        dealloc(filterCond1);
    }

    static void test_bound_relation() {

        std::cout << "bound relation\n";

        smt_params params;
        ast_manager ast_m;
        reg_decl_plugins(ast_m);
        register_engine re;
        context ctx(ast_m, re, params);    
        arith_util autil(ast_m);
        relation_manager & m = ctx.get_rel_context()->get_rmanager();
        m.register_plugin(alloc(bound_relation_plugin, m));
        bound_relation_plugin& br = dynamic_cast<bound_relation_plugin&>(*m.get_relation_plugin(symbol("bound_relation")));
        ENSURE(&br);
        
        relation_signature sig;
        sort* int_sort = autil.mk_int();
        sig.push_back(int_sort);
        sig.push_back(int_sort);
        sig.push_back(int_sort);
        sig.push_back(int_sort);

        bound_relation& i1 = dynamic_cast<bound_relation&>(*br.mk_empty(sig));
        bound_relation& i2 = dynamic_cast<bound_relation&>(*br.mk_full(0, sig));

        i1.display(std::cout << "empty:\n");
        i2.display(std::cout << "full:\n");
        ENSURE(i1.empty());
        ENSURE(!i2.empty());

        app_ref cond1(ast_m), cond2(ast_m), cond3(ast_m);
        app_ref cond4(ast_m), cond5(ast_m), cond6(ast_m);
        app_ref num1(ast_m);
        cond1 = autil.mk_lt(ast_m.mk_var(0, int_sort), autil.mk_numeral(rational(0), true));
        cond2 = autil.mk_lt(ast_m.mk_var(1, int_sort), autil.mk_numeral(rational(1), true));
        cond3 = autil.mk_lt(ast_m.mk_var(2, int_sort), ast_m.mk_var(3, int_sort));
        cond4 = autil.mk_ge(ast_m.mk_var(0, int_sort), autil.mk_numeral(rational(0), true));
        cond5 = autil.mk_ge(ast_m.mk_var(1, int_sort), autil.mk_numeral(rational(0), true));
        cond6 = autil.mk_ge(ast_m.mk_var(2, int_sort), autil.mk_numeral(rational(5), true));

        app_ref lt_x0x1(ast_m), lt_x1x2(ast_m), lt_x0x3(ast_m), lt_x0x2(ast_m);
        lt_x0x1 = autil.mk_lt(ast_m.mk_var(0, int_sort), ast_m.mk_var(1, int_sort));
        lt_x1x2 = autil.mk_lt(ast_m.mk_var(1, int_sort), ast_m.mk_var(2, int_sort));
        lt_x0x2 = autil.mk_lt(ast_m.mk_var(0, int_sort), ast_m.mk_var(2, int_sort));
        lt_x0x3 = autil.mk_lt(ast_m.mk_var(0, int_sort), ast_m.mk_var(3, int_sort));

        num1 = autil.mk_numeral(rational(4), true);
        
        unsigned cols1[2] = { 1, 2};
        unsigned cols2[2] = { 2, 3};
        unsigned cols3[3] = { 0, 2, 3 };
        relation_join_fn* join1 = br.mk_join_fn(i1, i2, 2, cols1, cols2);        
        relation_transformer_fn* proj1 = br.mk_project_fn(i1, 2, cols2);
        relation_transformer_fn* ren1  = br.mk_rename_fn(i1, 3, cols3);
        relation_union_fn*       union1 = br.mk_union_fn(i1, i2, &i1);
        relation_mutator_fn*     filterId1 = br.mk_filter_identical_fn(i1, 2, cols1);
        relation_mutator_fn*     filterEq1 = br.mk_filter_equal_fn(i1, num1, 2);               
        relation_mutator_fn*     filterCond1 = br.mk_filter_interpreted_fn(i1, cond3);

        relation_base* i3 = (*join1)(i2, i2);
        i3->display(std::cout);       
 
        relation_transformer_fn* proj2 = br.mk_project_fn(*i3, 2, cols2);

        (*filterEq1)(i2);
        i2.display(std::cout << "no-op still full\n");
        // no-op
        
        (*filterCond1)(i2);
        i2.display(std::cout << "x2 < x3\n");
        // x2 < x3

        (*filterId1)(i2);
        i2.display(std::cout << "id\n");
        // x1 = x2 < x3    
        relation_fact fact1(ast_m);

        i2.display(std::cout << "Orig\n");
        std::cout << "renamed ";
        for (unsigned i = 0; i < 3; ++i) {
            std::cout << cols3[i] << " ";
        }
        std::cout << "\n";
        relation_base* i5 = (*ren1)(i2);
        i5->display(std::cout);

        //ENSURE(i2.empty());

        relation_base* i4 = (*proj2)(*i3);
        i4->display(std::cout);      

        // test that equivalence classes are expanded.
        // { x1 = x3, x0 < x1 x1 < x2} u { x2 = x3, x0 < x3 } = { x0 < x3 }
        {
            relation_base* b1 = br.mk_full(0, sig);
            relation_base* b2 = br.mk_full(0, sig);
            unsigned x1x3[2] = { 1, 3 };
            unsigned x2x3[2] = { 2, 3 };
            scoped_ptr<relation_mutator_fn> id1 = br.mk_filter_identical_fn(*b1, 2, x1x3);
            scoped_ptr<relation_mutator_fn> ltx0x1 = br.mk_filter_interpreted_fn(*b1, lt_x0x1);
            scoped_ptr<relation_mutator_fn> ltx1x2 = br.mk_filter_interpreted_fn(*b1, lt_x1x2);
            scoped_ptr<relation_mutator_fn> ltx0x3 = br.mk_filter_interpreted_fn(*b2, lt_x0x3);
            scoped_ptr<relation_mutator_fn> id2 = br.mk_filter_identical_fn(*b2, 2, x2x3);
            (*id1)(*b1);
            (*ltx0x1)(*b1);
            (*ltx1x2)(*b1);
            b2->display(std::cout << "b2:\n");
            (*id2)(*b2);
            b2->display(std::cout << "b2:\n");
            (*ltx0x3)(*b2);
            b2->display(std::cout << "b2:\n");
            scoped_ptr<relation_union_fn> u = br.mk_union_fn(*b1, *b2, 0);
            b1->display(std::cout << "b1:\n");
            b2->display(std::cout << "b2:\n");
            (*u)(*b1, *b2, 0);

            b1->display(std::cout << "b1 u b2:\n");

            // TBD check property;
            
            b1->deallocate();
            b2->deallocate();
        }

        // test that equivalence classes are expanded.
        // { x1 = x2 = x3, x0 < x1} u { x1 = x3, x0 < x3, x0 < x2 } = { x0 < x2, x0 < x3 }
        {
            relation_base* b1 = br.mk_full(0, sig);
            relation_base* b2 = br.mk_full(0, sig);
            unsigned x0x3[2] = { 0, 3 };
            unsigned x1x3[2] = { 1, 3 };
            unsigned x2x3[2] = { 2, 3 };
            scoped_ptr<relation_mutator_fn> id1 = br.mk_filter_identical_fn(*b1, 2, x1x3);
            scoped_ptr<relation_mutator_fn> id2 = br.mk_filter_identical_fn(*b1, 2, x2x3);
            scoped_ptr<relation_mutator_fn> ltx0x1 = br.mk_filter_interpreted_fn(*b1, lt_x0x1);
            scoped_ptr<relation_mutator_fn> ltx0x2 = br.mk_filter_interpreted_fn(*b2, lt_x0x2);
            scoped_ptr<relation_mutator_fn> ltx0x3 = br.mk_filter_interpreted_fn(*b2, lt_x0x3);
            scoped_ptr<relation_mutator_fn> id3 = br.mk_filter_identical_fn(*b2, 2, x1x3);
            (*id1)(*b1);
            (*id2)(*b1);
            (*ltx0x1)(*b1);
            (*id3)(*b2);
            (*ltx0x2)(*b2);
            (*ltx0x3)(*b2);
            scoped_ptr<relation_union_fn> u = br.mk_union_fn(*b1, *b2, 0);
            b1->display(std::cout << "b1:\n");
            b2->display(std::cout << "b2:\n");
            (*u)(*b1, *b2, 0);
            b1->display(std::cout << "b1 u b2:\n");

            // TBD check property;
            
            b1->deallocate();
            b2->deallocate();
        }
        
        i1.deallocate();
        i2.deallocate();
        i3->deallocate();
        i4->deallocate();
        i5->deallocate();
        dealloc(join1);
        dealloc(proj1);
        dealloc(ren1);
        dealloc(union1);
        dealloc(filterId1);
        dealloc(filterEq1);
        dealloc(filterCond1);
    }

}

void tst_dl_relation() {
    datalog::test_interval_relation();
    datalog::test_bound_relation();
}

#else
void tst_dl_relation() {
}
#endif
