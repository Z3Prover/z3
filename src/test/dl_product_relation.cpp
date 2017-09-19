
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#ifdef _WINDOWS
#include "muz/base/dl_context.h"
#include "muz/fp/dl_register_engine.h"
#include "muz/rel/dl_finite_product_relation.h"
#include "muz/rel/dl_sparse_table.h"
#include "muz/rel/rel_context.h"

namespace datalog {


    typedef scoped_rel<table_base> table_aptr;

    class collector_of_reduced : public table_row_pair_reduce_fn {
        idx_set & m_acc;
    public:
        collector_of_reduced(idx_set & accumulator) : m_acc(accumulator) {}

        virtual void operator()(table_element * func_columns, const table_element * merged_func_columns) {
            m_acc.insert(static_cast<unsigned>(merged_func_columns[0]));
        }
    };


    void test_functional_columns(smt_params fparams, params_ref& params) {
        ast_manager m;
        register_engine re;
        context ctx(m, re, fparams);
        rel_context_base& rctx = *ctx.get_rel_context();
        ctx.updt_params(params);
        relation_manager & rmgr(rctx.get_rmanager());

        sparse_table_plugin & plugin = 
            static_cast<sparse_table_plugin &>(*rctx.get_rmanager().get_table_plugin(symbol("sparse")));
        ENSURE(&plugin);
        table_signature sig2;
        sig2.push_back(2);
        sig2.push_back(2);
        sig2.set_functional_columns(1);
        ENSURE(plugin.can_handle_signature(sig2));
        
        table_fact f00;
        f00.push_back(0);
        f00.push_back(0);
        table_fact f01;
        f01.push_back(0);
        f01.push_back(1);
        table_fact f11;
        f11.push_back(1);
        f11.push_back(1);

        {
            table_aptr t0 = plugin.mk_empty(sig2);
            ENSURE(t0->empty());
            t0->add_fact(f00);
            ENSURE(!t0->empty());
            ENSURE(t0->get_size_estimate_rows()==1);
            t0->add_fact(f01);
            ENSURE(t0->get_size_estimate_rows()==1);
            t0->add_fact(f11);
            ENSURE(t0->get_size_estimate_rows()==2);

            unsigned rem_cols0[]={0};
            scoped_ptr<table_transformer_fn> project0 = rmgr.mk_project_fn(*t0, 1, rem_cols0);
            table_aptr t1 = (*project0)(*t0);
            ENSURE(t1->get_size_estimate_rows()==2);
            ENSURE(t1->get_signature().functional_columns()==0); //project on non-functional column cancels functional

            unsigned rem_cols1[]={1};
            scoped_ptr<table_transformer_fn> project1 = rmgr.mk_project_fn(*t0, 1, rem_cols1);
            table_aptr t2 = (*project1)(*t0);
            ENSURE(t2->get_size_estimate_rows()==2);

            idx_set acc;
            collector_of_reduced * reducer = alloc(collector_of_reduced, acc);
            scoped_ptr<table_transformer_fn> rproject = rmgr.mk_project_with_reduce_fn(*t0, 1, rem_cols0, reducer);
            table_aptr rt = (*rproject)(*t0);
            ENSURE(acc.num_elems()==1);
            ENSURE(rt->get_size_estimate_rows()==1);
        }
        {
            table_aptr t0 = plugin.mk_empty(sig2);
            t0->add_fact(f01);

            unsigned join_cols[]={1};
            scoped_ptr<table_join_fn> join0 = rmgr.mk_join_fn(*t0, *t0, 1, join_cols, join_cols);
            table_aptr t1 = (*join0)(*t0, *t0);
            ENSURE(t1->get_signature().size()==4);
            ENSURE(t1->get_signature().functional_columns()==2);

            table_fact f0011;
            f0011.push_back(0);
            f0011.push_back(0);
            f0011.push_back(1);
            f0011.push_back(1);
            ENSURE(t1->contains_fact(f0011));
            table_fact f0111 = f0011;
            f0111[1] = 1;
            ENSURE(!t1->contains_fact(f0111));
        }

        {
            table_aptr t0 = plugin.mk_empty(sig2);
            t0->display(std::cout<<"0:");
            ENSURE(t0->get_signature().functional_columns()==1);
            
            table_fact aux_fact;

            aux_fact = f01;
            TRUSTME( t0->suggest_fact(aux_fact) );
            t0->display(std::cout<<"1:");
            ENSURE(t0->contains_fact(f01));
            ENSURE(aux_fact[1]==1);

            aux_fact = f00;
            TRUSTME( !t0->suggest_fact(aux_fact) );
            t0->display(std::cout<<"2:");
            ENSURE(t0->contains_fact(f01));
            ENSURE(!t0->contains_fact(f00));
            ENSURE(aux_fact[1]==1);

            t0->ensure_fact(f00);
            t0->display(std::cout<<"3:");
            ENSURE(t0->contains_fact(f00));
            ENSURE(!t0->contains_fact(f01));
        }
    }

    void test_finite_product_relation(smt_params fparams, params_ref& params) {
        ast_manager m;
        register_engine re;
        context ctx(m, re, fparams);
        ctx.updt_params(params);
        dl_decl_util dl_util(m);
        relation_manager & rmgr = ctx.get_rel_context()->get_rmanager();

        relation_plugin & rel_plugin = *rmgr.get_relation_plugin(params.get_sym("default_relation", symbol("sparse")));
        ENSURE(&rel_plugin);
        finite_product_relation_plugin plg(rel_plugin, rmgr);

        sort_ref byte_srt_ref(dl_util.mk_sort(symbol("BYTE"), 256), m);
        relation_sort byte_srt = byte_srt_ref;

        relation_signature sig2;
        sig2.push_back(byte_srt);
        sig2.push_back(byte_srt);
        relation_signature sig3(sig2);
        sig3.push_back(byte_srt);
        relation_signature sig4(sig3);
        sig4.push_back(byte_srt);

        app_ref seven_ref(dl_util.mk_numeral(7, byte_srt), m);
        app_ref nine_ref(dl_util.mk_numeral(9, byte_srt), m);

        relation_element seven = seven_ref;
        relation_element nine = nine_ref;

        relation_fact f7(m);
        f7.push_back(seven);
        relation_fact f9(m);
        f9.push_back(nine);

        relation_fact f77(f7);
        f77.push_back(seven);
        relation_fact f79(f7);
        f79.push_back(nine);
        relation_fact f97(f9);
        f97.push_back(seven);
        relation_fact f99(f9);
        f99.push_back(nine);

        relation_fact f779(f77);
        f779.push_back(nine);
        relation_fact f799(f79);
        f799.push_back(nine);
        relation_fact f977(f97);
        f977.push_back(seven);

        relation_fact f7797(f779);
        f7797.push_back(seven);
        relation_fact f7997(f799);
        f7997.push_back(seven);


        bool table_cols2[] = { true, false };
        bool table_cols3[] = { true, false, false };
        bool table_cols4[] = { true, true, false, false };
        scoped_rel<relation_base> r1 = plg.mk_empty(sig2, table_cols2);
        scoped_rel<relation_base> r2 = r1->clone();
        scoped_rel<relation_base> r3 = r2->clone();

        ENSURE(!r1->contains_fact(f77));
        r1->add_fact(f77);
        ENSURE(r1->contains_fact(f77));

        r2->add_fact(f79);
        r3->add_fact(f99);


        r2->display( std::cout << "r2 0\n");
        scoped_rel<relation_base> r4 = r2->clone();
        r2->display( std::cout << "r2 1\n");

        r4->display( std::cout << "r4 0\n");
        ENSURE(!r4->contains_fact(f77));
        ENSURE(r4->contains_fact(f79));
        r4->add_fact(f77);
        r4->display( std::cout << "r4 1\n");
        ENSURE(r4->contains_fact(f77));
        ENSURE(r4->contains_fact(f79));
        r4->add_fact(f99);
        r4->display( std::cout << "r4 2\n");
        ENSURE(r4->contains_fact(f99));


        std::cout << "------ testing union ------\n";
        r2->display( std::cout << "r2\n");
        scoped_ptr<relation_union_fn> union_op = rmgr.mk_union_fn(*r1, *r2, r3.get());
        ENSURE(union_op);
        (*union_op)(*r1, *r2, r3.get());

        r1->display( std::cout << "r1\n");
        r2->display( std::cout << "r2\n");
        r3->display( std::cout << "r3\n");

        ENSURE(r1->contains_fact(f77));
        ENSURE(r1->contains_fact(f79));
        ENSURE(!r1->contains_fact(f99));

        ENSURE(!r3->contains_fact(f77));
        ENSURE(r3->contains_fact(f79));
        ENSURE(r3->contains_fact(f99));

        std::cout << "------ testing join ------\n";

        r1->reset();
        r1->add_fact(f77);
        r1->add_fact(f79);
        r1->add_fact(f97);
        r2->reset();
        r2->add_fact(f97);
        r2->add_fact(f99);

        unsigned col0[] = { 0 };
        unsigned col1[] = { 1 };
        scoped_ptr<relation_join_fn> join_tt = rmgr.mk_join_fn(*r1, *r2, 1, col0, col0);
        scoped_ptr<relation_join_fn> join_tr = rmgr.mk_join_fn(*r1, *r2, 1, col0, col1);
        scoped_ptr<relation_join_fn> join_rr = rmgr.mk_join_fn(*r1, *r2, 1, col1, col1);

        r1->display( std::cout << "r1\n");
        r2->display( std::cout << "r2\n");

        scoped_rel<relation_base> jr_tt = (*join_tt)(*r1, *r2);
        scoped_rel<relation_base> jr_tr = (*join_tr)(*r1, *r2);
        scoped_rel<relation_base> jr_rr = (*join_rr)(*r1, *r2);

        jr_tt->display( std::cout << "tt\n");
        jr_tr->display( std::cout << "tr\n");
        jr_rr->display( std::cout << "rr\n");


        ENSURE(!jr_tt->contains_fact(f7797));
        ENSURE(jr_tr->contains_fact(f7797));
        ENSURE(jr_rr->contains_fact(f7797));


        std::cout << "------ testing project ------\n";

        scoped_rel<relation_base> r31 = plg.mk_empty(sig3, table_cols3);
        r31->add_fact(f779);
        r31->add_fact(f977);
        r31->add_fact(f799);
        
        unsigned rem_1_rel[] = { 1 };
        unsigned rem_2_rel[] = { 1, 2 };
        unsigned rem_1_table[] = { 0 };

        scoped_ptr<relation_transformer_fn> proj_1r = rmgr.mk_project_fn(*r31, 1, rem_1_rel);
        scoped_ptr<relation_transformer_fn> proj_2r = rmgr.mk_project_fn(*r31, 2, rem_2_rel);
        scoped_ptr<relation_transformer_fn> proj_1t = rmgr.mk_project_fn(*r31, 1, rem_1_table);

        scoped_rel<relation_base> sr_1r = (*proj_1r)(*r31);
        scoped_rel<relation_base> sr_2r = (*proj_2r)(*r31);
        scoped_rel<relation_base> sr_1t = (*proj_1t)(*r31);

        ENSURE(sr_1r->contains_fact(f79));
        ENSURE(sr_1r->contains_fact(f97));
        ENSURE(!sr_1r->contains_fact(f77));

        ENSURE(sr_2r->contains_fact(f7));
        ENSURE(sr_2r->contains_fact(f9));

        ENSURE(sr_1t->contains_fact(f79));
        ENSURE(!sr_1t->contains_fact(f97));
        ENSURE(sr_1t->contains_fact(f77));
        ENSURE(sr_1t->contains_fact(f99));

        std::cout << "------ testing filter_interpreted ------\n";

        scoped_rel<relation_base> r41 = plg.mk_empty(sig4, table_cols4);

        r41->add_fact(f7797);
        r41->add_fact(f7997);

        app_ref cond(m.mk_and(
                m.mk_not(m.mk_eq(m.mk_var(1,byte_srt), m.mk_var(2,byte_srt))), //#1!=#2
                m.mk_not(m.mk_eq(m.mk_var(3,byte_srt), m.mk_var(2,byte_srt)))  //#3!=#2
            ), m);
        scoped_ptr<relation_mutator_fn> i_filter = rmgr.mk_filter_interpreted_fn(*r41, cond);
        (*i_filter)(*r41);

        ENSURE(r41->contains_fact(f7797));
        ENSURE(!r41->contains_fact(f7997));

        std::cout << "------ testing filter_by_negation ------\n";

        r31->reset();
        r31->add_fact(f779);
        r31->add_fact(f977);
        r31->add_fact(f799);

        r1->reset();
        r1->add_fact(f77);
        r1->add_fact(f79);

        unsigned nf_r31_cols[] = {1, 0, 1};
        unsigned nf_r1_cols[] = {0, 0, 1};
        scoped_ptr<relation_intersection_filter_fn> neg_filter = rmgr.mk_filter_by_negation_fn(*r31, *r1, 3,
            nf_r31_cols, nf_r1_cols);
        (*neg_filter)(*r31, *r1);

        ENSURE(!r31->contains_fact(f779));
        ENSURE(r31->contains_fact(f977));
        ENSURE(r31->contains_fact(f799));


    }
}





using namespace datalog;

void tst_dl_product_relation() {
    smt_params fparams;
    params_ref params;

    test_functional_columns(fparams, params);

    params.set_sym("default_relation", symbol("tr_sparse"));
    test_finite_product_relation(fparams, params);
    
}
#else
void tst_dl_product_relation() {
}
#endif
