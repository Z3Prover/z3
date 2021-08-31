
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "muz/rel/udoc_relation.h"
#include "util/trace.h"
#include "util/vector.h"
#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/reg_decl_plugins.h"
#include "util/sorting_network.h"
#include "smt/smt_kernel.h"
#include "model/model_smt2_pp.h"
#include "smt/params/smt_params.h"
#include "ast/ast_util.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/rewriter/th_rewriter.h"
#include "muz/rel/dl_relation_manager.h"
#include "muz/fp/dl_register_engine.h"
#include "muz/rel/rel_context.h"
#include "ast/bv_decl_plugin.h"
#include "muz/rel/check_relation.h"


class udoc_tester {
    typedef datalog::relation_base relation_base;
    typedef datalog::udoc_relation udoc_relation;
    typedef datalog::udoc_plugin   udoc_plugin;
    typedef datalog::relation_signature relation_signature;
    typedef datalog::relation_fact relation_fact;
    typedef scoped_ptr<datalog::relation_mutator_fn> rel_mut;
    typedef scoped_ptr<datalog::relation_union_fn> rel_union;

    struct init {
        init(ast_manager& m) {
            reg_decl_plugins(m);
        }
    };
    random_gen                m_rand;
    ast_manager               m;
    init                      m_init;
    bv_util                   bv;
    expr_ref_vector           m_vars;
    smt_params                m_smt_params;
    datalog::register_engine  m_reg;
    datalog::context          m_ctx;
    datalog::rel_context      rc;
    udoc_plugin&              p;
    datalog::check_relation_plugin&           cr;


    tbit choose_tbit() {
        switch (m_rand(3)) {
        case 0: return BIT_0;
        case 1: return BIT_1;
        default : return BIT_x;
        }
    }

    tbv* mk_rand_tbv(doc_manager& dm) {
        tbv* result = dm.tbvm().allocate();
        for (unsigned i = 0; i < dm.num_tbits(); ++i) {
            dm.tbvm().set(*result, i, choose_tbit());
        }
        return result;
    }

    tbv* mk_rand_tbv(doc_manager& dm, tbv const& pos) {
        tbv* result = dm.tbvm().allocate();
        for (unsigned i = 0; i < dm.num_tbits(); ++i) {
            if (pos[i] == BIT_x) {
                dm.tbvm().set(*result, i, choose_tbit());
            }
            else {
                dm.tbvm().set(*result, i, pos[i]);
            }
        }
        return result;
    }
    
    doc* mk_rand_doc(doc_manager& dm, unsigned num_diff) {
        tbv_ref t(dm.tbvm());
        doc_ref result(dm);
        t = mk_rand_tbv(dm);
        result = dm.allocate(*t);
        ENSURE(dm.tbvm().equals(*t, result->pos()));
        for (unsigned i = 0; i < num_diff; ++i) {
            t = mk_rand_tbv(dm, result->pos());
            if (dm.tbvm().equals(*t, result->pos())) {
                return nullptr;
            }
            if (!result->neg().is_empty() &&
                dm.tbvm().equals(*t, result->neg()[0])) {
                continue;
            }
            result->neg().push_back(t.detach());            
        }        
        ENSURE(dm.well_formed(*result));
        return result.detach();
    }

    void mk_rand_udoc(doc_manager& dm, unsigned num_elems, unsigned num_diff, udoc& result) {
        result.reset(dm);
        for (unsigned i = 0; i < num_elems; ++i) {
            doc* d = mk_rand_doc(dm, num_diff);
            if (d) {
                result.push_back(d);
            }
        }
    }

public:
    udoc_tester(): 
        m_init(m), bv(m), m_vars(m), m_ctx(m, m_reg, m_smt_params), rc(m_ctx),
        p(dynamic_cast<udoc_plugin&>(*rc.get_rmanager().get_relation_plugin(symbol("doc")))),
        cr(dynamic_cast<datalog::check_relation_plugin&>(*rc.get_rmanager().get_relation_plugin(symbol("check_relation"))))
    {   
        cr.set_plugin(&p);
    }

    udoc_relation* mk_empty(relation_signature const& sig) {
        ENSURE(p.can_handle_signature(sig));
        relation_base* empty = p.mk_empty(sig);
        return dynamic_cast<udoc_relation*>(empty);
    }

    udoc_relation* mk_full(relation_signature const& sig) {
        func_decl_ref fn(m);
        fn = m.mk_func_decl(symbol("full"), sig.size(), sig.data(), m.mk_bool_sort());
        relation_base* full = p.mk_full(fn, sig);
        return dynamic_cast<udoc_relation*>(full);
    }

    void test1() {
        datalog::relation_signature sig;
        sig.push_back(bv.mk_sort(12));
        sig.push_back(bv.mk_sort(6));
        sig.push_back(bv.mk_sort(12));
        

        datalog::relation_fact fact1(m), fact2(m), fact3(m);
        fact1.push_back(bv.mk_numeral(rational(1), 12));
        fact1.push_back(bv.mk_numeral(rational(6), 6));
        fact1.push_back(bv.mk_numeral(rational(56), 12));
        fact2.push_back(bv.mk_numeral(rational(8), 12));
        fact2.push_back(bv.mk_numeral(rational(16), 6));
        fact2.push_back(bv.mk_numeral(rational(32), 12));
        fact3.push_back(bv.mk_numeral(rational(32), 12));
        fact3.push_back(bv.mk_numeral(rational(16), 6));
        fact3.push_back(bv.mk_numeral(rational(4), 12));

        relation_signature sig2;
        sig2.push_back(bv.mk_sort(3));
        sig2.push_back(bv.mk_sort(6));
        sig2.push_back(bv.mk_sort(3));
        sig2.push_back(bv.mk_sort(3));
        sig2.push_back(bv.mk_sort(3));

        relation_base* t;
        udoc_relation* t1, *t2, *t3;
        expr_ref fml(m);

        test_filter_neg2();

        test_join_project();
        test_join_project2();
        test_join_project3();

        test_filter_neg4(false);
        test_filter_neg4(true);
        test_filter_neg5(false);
        test_filter_neg5(true);

        test_filter_neg();
        test_filter_neg3();

        test_join(1000);

        test_rename();


        // empty
        {
            std::cout << "empty\n";
            t = mk_empty(sig);
            t->display(std::cout); std::cout << "\n";
            t->to_formula(fml);
            std::cout << fml << "\n";
            t->deallocate();
        }

        // full
        {
            std::cout << "full\n";
            t = mk_full(sig);
            t->display(std::cout); std::cout << "\n";
            t->to_formula(fml);
            std::cout << fml << "\n";
            t->deallocate();
        }

        // join
        {
            t1 = mk_full(sig);
            t2 = mk_full(sig);
            t3 = mk_empty(sig);
            unsigned_vector jc1, jc2;
            jc1.push_back(1);
            jc2.push_back(1);
            datalog::relation_join_fn* join_fn = p.mk_join_fn(*t1, *t2, jc1.size(), jc1.data(), jc2.data());
            ENSURE(join_fn);
            t = (*join_fn)(*t1, *t2);
            cr.verify_join(*t1, *t2, *t, jc1, jc2);
            t->display(std::cout); std::cout << "\n";
            t->deallocate();

            t = (*join_fn)(*t1, *t3);
            cr.verify_join(*t1, *t3, *t, jc1, jc2);
            ENSURE(t->empty());
            t->display(std::cout); std::cout << "\n";
            t->deallocate();

            t = (*join_fn)(*t3, *t3);
            cr.verify_join(*t3, *t3, *t, jc1, jc2);
            ENSURE(t->empty());
            t->display(std::cout); std::cout << "\n";
            t->deallocate();
                       
            dealloc(join_fn);
            t1->deallocate();
            t2->deallocate();
            t3->deallocate();
        }

        // project
        {
            std::cout << "project\n";
            t1 = mk_full(sig);
            unsigned_vector pc;
            pc.push_back(0);
            datalog::relation_transformer_fn* proj_fn = p.mk_project_fn(*t1, pc.size(), pc.data());
            t = (*proj_fn)(*t1);
            cr.verify_project(*t1, *t, pc);
            t->display(std::cout); std::cout << "\n";
            t->deallocate();
            
            t1->reset();
            t = (*proj_fn)(*t1);
            cr.verify_project(*t1, *t, pc);
            t->display(std::cout); std::cout << "\n";
            t->deallocate();
            
            t1->add_fact(fact1);
            t1->add_fact(fact2);
            t1->add_fact(fact3);
            t = (*proj_fn)(*t1);
            cr.verify_project(*t1, *t, pc);
            t1->display(std::cout); std::cout << "\n";
            t->display(std::cout); std::cout << "\n";
            t->deallocate();

            dealloc(proj_fn);
            t1->deallocate();
        }

        // union
        {
            t1 = mk_empty(sig);
            t2 = mk_empty(sig);
            udoc_relation* delta = mk_full(sig);
            t2->add_fact(fact1);
            t2->add_fact(fact2);
            t1->add_fact(fact3);

            expr_ref t10(m);
            t1->to_formula(t10);
            expr_ref delta0(m);
            delta->to_formula(delta0);
            rel_union union_fn = p.mk_union_fn(*t1, *t2, nullptr);

            t1->display(std::cout << "t1 before:"); std::cout << "\n";
            (*union_fn)(*t1, *t2, delta);
            cr.verify_union(t10, *t2, *t1, delta0, delta);
            t1->display(std::cout << "t1 after:"); std::cout << "\n";
            delta->display(std::cout << "delta:"); std::cout << "\n";
            
            t1->deallocate();
            t2->deallocate();
            delta->deallocate();
        }

        // filter_identical
        {
            t1 = mk_empty(sig2);
            unsigned_vector id;
            id.push_back(0);
            id.push_back(2);
            id.push_back(4);
            rel_mut filter_id = p.mk_filter_identical_fn(*t1, id.size(), id.data());
            relation_fact f1(m);
            f1.push_back(bv.mk_numeral(rational(1),3));
            f1.push_back(bv.mk_numeral(rational(1),6));
            f1.push_back(bv.mk_numeral(rational(1),3));
            f1.push_back(bv.mk_numeral(rational(1),3));
            f1.push_back(bv.mk_numeral(rational(1),3));
            t1->add_fact(f1);
            f1[4] = bv.mk_numeral(rational(2),3);
            t1->add_fact(f1);
            t1->display(std::cout); std::cout << "\n";
            (*filter_id)(*t1);
            t1->display(std::cout); std::cout << "\n";
            t1->deallocate();
        }
        
        // tbv_manager::debug_alloc();
        {
            relation_signature sig3;
            sig3.push_back(m.mk_bool_sort());
            sig3.push_back(m.mk_bool_sort());
            sig3.push_back(m.mk_bool_sort());
            var_ref v0(m.mk_var(0, m.mk_bool_sort()),m);
            var_ref v1(m.mk_var(1, m.mk_bool_sort()),m);
            var_ref v2(m.mk_var(2, m.mk_bool_sort()),m);
            app_ref cond1(m);
            t1 = mk_full(sig3);
            cond1 = m.mk_eq(v0,v1);
            apply_filter(*t1, cond1);
            t1->deallocate();
        }

        {
            relation_signature sig3;
            sig3.push_back(m.mk_bool_sort());
            sig3.push_back(m.mk_bool_sort());
            sig3.push_back(m.mk_bool_sort());
            var_ref v0(m.mk_var(0, m.mk_bool_sort()),m);
            var_ref v1(m.mk_var(1, m.mk_bool_sort()),m);
            var_ref v2(m.mk_var(2, m.mk_bool_sort()),m);
            app_ref cond1(m);
            t1 = mk_full(sig3);
            cond1 = m.mk_or(m.mk_eq(v0,v1),m.mk_eq(v0,v2));
            apply_filter(*t1, cond1);
            t1->deallocate();
        }

        {
            relation_signature sig3;
            sig3.push_back(bv.mk_sort(1));
            sig3.push_back(bv.mk_sort(1));
            sig3.push_back(bv.mk_sort(1));
            var_ref v0(m.mk_var(0, bv.mk_sort(1)),m);
            var_ref v1(m.mk_var(1, bv.mk_sort(1)),m);
            var_ref v2(m.mk_var(2, bv.mk_sort(1)),m);
            app_ref cond1(m);
            cond1 = m.mk_or(m.mk_eq(v0,v1),m.mk_eq(v0,v2));
            t1 = mk_full(sig3);
            apply_filter(*t1, cond1);
            t1->deallocate();
        }


        app_ref_vector conds(m);
        app_ref cond1(m);
        var_ref v0(m.mk_var(0, bv.mk_sort(3)),m);
        var_ref v1(m.mk_var(1, bv.mk_sort(6)),m);
        var_ref v2(m.mk_var(2, bv.mk_sort(3)),m);
        var_ref v3(m.mk_var(3, bv.mk_sort(3)),m);
        var_ref v4(m.mk_var(4, bv.mk_sort(3)),m);
        conds.push_back(m.mk_true());
        conds.push_back(m.mk_false());
        conds.push_back(m.mk_eq(v0, v2));
        conds.push_back(m.mk_not(m.mk_eq(v0, v2)));
        conds.push_back(m.mk_eq(v0, bv.mk_numeral(rational(2), 3)));
        cond1 = m.mk_eq(ex(2,1,v0),bv.mk_numeral(rational(3),2));
        conds.push_back(cond1);
        conds.push_back(m.mk_or(cond1,m.mk_eq(v3,v4)));
        conds.push_back(m.mk_eq(ex(2,1,v3),ex(1,0,v4)));
        conds.push_back(m.mk_or(cond1,m.mk_eq(ex(2,1,v3),ex(1,0,v4))));
        conds.push_back(m.mk_or(m.mk_eq(v0,v2),m.mk_eq(v0,v4)));
        conds.push_back(m.mk_or(m.mk_eq(v0,v2),m.mk_eq(v3,v4)));
        conds.push_back(m.mk_or(m.mk_eq(ex(2,1,v0),ex(1,0,v2)),m.mk_eq(v3,v4)));
        conds.push_back(m.mk_or(m.mk_eq(ex(2,1,v0),bv.mk_numeral(rational(3),2)), 
                                m.mk_eq(v3,v4)));
        conds.push_back(m.mk_or(m.mk_eq(ex(2,1,v0),bv.mk_numeral(rational(3),2)), 
                                m.mk_eq(v3,bv.mk_numeral(rational(3),3))));
        conds.push_back(m.mk_or(m.mk_eq(v0,bv.mk_numeral(rational(5),3)), 
                                m.mk_eq(v3,bv.mk_numeral(rational(5),3))));
        conds.push_back(m.mk_or(m.mk_eq(v0,bv.mk_numeral(rational(7),3)), 
                                m.mk_eq(v3,bv.mk_numeral(rational(7),3))));
        conds.push_back(m.mk_not(m.mk_or(m.mk_eq(v0,v2),m.mk_eq(v3,v4))));


        // filter_interpreted
        {
            std::cout << "filter interpreted\n";
            t1 = mk_full(sig2);

            for (unsigned i = 0; i < conds.size(); ++i) {
                apply_filter(*t1, conds[i].get());
            }
            
            t1->deallocate();

        }

        // filter_interpreted_project
        {
            unsigned_vector remove;
            remove.push_back(0);
            remove.push_back(2);

            t1 = mk_full(sig2);
            apply_filter(*t1, conds[2].get());
            apply_filter_project(*t1, remove, conds[2].get());
            apply_filter_project(*t1, remove, conds[3].get());
            t1->deallocate();

            t1 = mk_full(sig2);
            apply_filter(*t1, conds[3].get());
            apply_filter_project(*t1, remove, conds[2].get());
            apply_filter_project(*t1, remove, conds[3].get());
            t1->deallocate();

            for (unsigned i = 0; i < conds.size(); ++i) {
                t1 = mk_full(sig2);
                apply_filter_project(*t1, remove, conds[i].get());
                t1->deallocate();
            }

            remove[1] = 1;
            for (unsigned i = 0; i < conds.size(); ++i) {
                t1 = mk_full(sig2);
                apply_filter_project(*t1, remove, conds[i].get());
                t1->deallocate();
            }
        }


    }

    // {11xx \ {111x}, x011 \ {x011}, 0111}
    // {xx11 \ {0011, 1111, x111}}
    // 0111
    // {1x1x \ {1x1x}, 1111 \ {1111}, x1x1 \ {x1x1}}

    void test_join_project() 
    {
        datalog::relation_signature sig;
        sig.push_back(bv.mk_sort(2));
        sig.push_back(bv.mk_sort(2));
        //sig.push_back(bv.mk_sort(3));
        
        unsigned_vector jc1, jc2, pc;
        jc1.push_back(0);
        jc2.push_back(0);
        pc.push_back(1);
        pc.push_back(3);
        //pc.push_back(4);        
        udoc_relation* t1, *t2;
        relation_base* t;

        scoped_ptr<datalog::relation_join_fn> join_project_fn;

        for (unsigned i = 0; i < 200; ++i) {
            t1 = mk_rand(sig);
            t2 = mk_rand(sig);
            t1->display(std::cout);
            t2->display(std::cout);
            join_project_fn = p.mk_join_project_fn(*t1, *t2, jc1.size(), jc1.data(), jc2.data(), pc.size(), pc.data());
            t = (*join_project_fn)(*t1, *t2);
            t->display(std::cout);
            cr.verify_join_project(*t1, *t2, *t, jc1, jc2, pc);
            t->deallocate();
            t1->deallocate();
            t2->deallocate();
        }
    }

    void test_join_project2()
    {
        relation_signature sig3;
        sig3.push_back(bv.mk_sort(1));
        sig3.push_back(bv.mk_sort(1));
        sig3.push_back(bv.mk_sort(1));

        /// xxx \ x11
        udoc_relation *t1 = mk_full(sig3);
        {
            udoc_relation *neg = mk_full(sig3);
            doc& n = neg->get_udoc()[0];
            neg->get_dm().set(n, 1, BIT_1);
            neg->get_dm().set(n, 2, BIT_1);

            unsigned_vector allcols;
            allcols.push_back(0);
            allcols.push_back(1);
            allcols.push_back(2);
            apply_filter_neg(*t1, *neg, allcols, allcols);
            neg->deallocate();
        }

        // 11x
        udoc_relation *t2 = mk_full(sig3);
        {
            doc& n = t2->get_udoc()[0];
            t2->get_dm().set(n, 0, BIT_1);
            t2->get_dm().set(n, 1, BIT_1);
        }

        unsigned_vector jc1, jc2, pc;
        jc1.push_back(1);
        jc1.push_back(2);
        jc2.push_back(0);
        jc2.push_back(1);
        pc.push_back(1);
        pc.push_back(2);

        scoped_ptr<datalog::relation_join_fn> join_project_fn;
        join_project_fn = p.mk_join_project_fn(*t1, *t2, jc1.size(), jc1.data(), jc2.data(), pc.size(), pc.data());
        relation_base *t = (*join_project_fn)(*t1, *t2);
        cr.verify_join_project(*t1, *t2, *t, jc1, jc2, pc);
        t->deallocate();
        t1->deallocate();
        t2->deallocate();
    }

    void test_join_project3()
    {
      datalog::relation_signature sig;
      sig.push_back(bv.mk_sort(2));
      sig.push_back(bv.mk_sort(2));

      unsigned_vector jc1, jc2, pc;
      jc1.push_back(0);
      jc1.push_back(1);
      jc2.push_back(1);
      jc2.push_back(0);
      pc.push_back(0);
      pc.push_back(1);     

      scoped_ptr<datalog::relation_join_fn> join_project_fn;

      udoc_relation* t1 = mk_empty(sig);
      {
        datalog::relation_fact fact1(m);
        fact1.push_back(bv.mk_numeral(rational(3), 2));
        fact1.push_back(bv.mk_numeral(rational(1), 2));
        t1->add_fact(fact1);
      }

      udoc_relation *t2 = mk_empty(sig);
      {
        datalog::relation_fact fact1(m);
        fact1.push_back(bv.mk_numeral(rational(0), 2));
        fact1.push_back(bv.mk_numeral(rational(3), 2));
        t2->add_fact(fact1);
        fact1.reset();
        fact1.push_back(bv.mk_numeral(rational(1), 2));
        fact1.push_back(bv.mk_numeral(rational(3), 2));
        t2->add_fact(fact1);
      }

      t1->display(std::cout << "t1:");
      t2->display(std::cout << "t2:");
      join_project_fn = p.mk_join_project_fn(*t1, *t2, jc1.size(), jc1.data(), jc2.data(), pc.size(), pc.data());

      relation_base* t;
      t = (*join_project_fn)(*t1, *t2);
      t->display(std::cout << "t:");
      cr.verify_join_project(*t1, *t2, *t, jc1, jc2, pc);
      t->deallocate();
      t1->deallocate();
      t2->deallocate();
    }

    void test_rename() {
        udoc_relation* t1;
        // rename
        datalog::relation_signature sig;
        sig.push_back(bv.mk_sort(12));
        sig.push_back(bv.mk_sort(6));
        sig.push_back(bv.mk_sort(2));
        datalog::relation_fact fact1(m);
        fact1.push_back(bv.mk_numeral(rational(1), 12));
        fact1.push_back(bv.mk_numeral(rational(6), 6));
        fact1.push_back(bv.mk_numeral(rational(3), 2));
        t1 = mk_empty(sig);
        t1->add_fact(fact1);
        unsigned_vector cycle;
        cycle.push_back(0);
        cycle.push_back(2);
        check_permutation(t1, cycle);

        sig.reset();
        sig.push_back(bv.mk_sort(2));
        sig.push_back(bv.mk_sort(6));
        sig.push_back(bv.mk_sort(12));
        fact1.reset();
        fact1.push_back(bv.mk_numeral(rational(3), 2));
        fact1.push_back(bv.mk_numeral(rational(6), 6));
        fact1.push_back(bv.mk_numeral(rational(1), 12));
        t1 = mk_empty(sig);
        t1->add_fact(fact1);
        cycle.reset();
        cycle.push_back(0);
        cycle.push_back(2);
        check_permutation(t1, cycle);

        t1 = mk_empty(sig);
        t1->add_fact(fact1);
        cycle.reset();
        cycle.push_back(0);
        cycle.push_back(1);
        cycle.push_back(2);
        check_permutation(t1, cycle);
    }

    void test_join(unsigned num_rounds) {
        for (unsigned i = 0; i < num_rounds; ++i) {
            test_join();
        }
    }

    void test_join() {
        relation_signature sig;
        sig.push_back(bv.mk_sort(2));
        sig.push_back(bv.mk_sort(3));
        udoc_relation* t1, *t2;
        relation_base* t;

        t1 = mk_rand(sig);
        t2 = mk_rand(sig);

        unsigned_vector jc1, jc2;
        jc1.push_back(0);
        jc2.push_back(0);
        scoped_ptr<datalog::relation_join_fn> join_fn;

        join_fn = p.mk_join_fn(*t1, *t2, jc1.size(), jc1.data(), jc2.data());
        t = (*join_fn)(*t1, *t2);

        cr.verify_join(*t1, *t2, *t, jc1, jc2);
        t1->display(std::cout);
        t2->display(std::cout);
        t->display(std::cout);
        std::cout << "\n";
        t1->deallocate();
        t2->deallocate();        
        t->deallocate();
    }

    udoc_relation* mk_rand(relation_signature const& sig) {
        udoc_relation* t = mk_empty(sig);
        mk_rand_udoc(t->get_dm(), 3, 3, t->get_udoc());
        return t;
    }

    void check_permutation(relation_base* t1, unsigned_vector const& cycle) {
        scoped_ptr<datalog::relation_transformer_fn> rename;
        rename = p.mk_rename_fn(*t1, cycle.size(), cycle.data());        
        relation_base* t = (*rename)(*t1);
        cr.verify_permutation(*t1,*t, cycle);
        t1->display(std::cout); std::cout << "\n";
        t->display(std::cout); std::cout << "\n";
        t->deallocate();            
        t1->deallocate();
    }

    /*
      The filter_by_negation postcondition:
      filter_by_negation(tgt, neg, columns in tgt: c1,...,cN, 
      corresponding columns in neg: d1,...,dN):
      tgt_1:={x: x\in tgt_0 && ! \exists y: ( y \in neg & pi_c1(x)= pi_d1(y) & ... & pi_cN(x)= pi_dN(y) ) }
    */

    void test_filter_neg() {
        // filter_by_negation

        relation_signature sig4;
        sig4.push_back(bv.mk_sort(1));
        sig4.push_back(bv.mk_sort(1));
        sig4.push_back(bv.mk_sort(1));
        udoc_relation* t1 = mk_empty(sig4);
        udoc_relation* t2 = mk_empty(sig4);
        unsigned_vector cols1, cols2;
        unsigned num_bits = t1->get_dm().num_tbits();
        
        cols1.push_back(0);
        cols2.push_back(1);
        for (unsigned i = 0; i < 100; ++i) {
            set_random(*t1, 2*num_bits/3);
            set_random(*t2, 2*num_bits/3);
            apply_filter_neg(*t1,*t2, cols1, cols2);
        }
        cols1.push_back(1);
        cols2.push_back(2);
        for (unsigned i = 0; i < 200; ++i) {
            set_random(*t1, 2*num_bits/3);
            set_random(*t2, 2*num_bits/3);
            apply_filter_neg(*t1,*t2, cols1, cols2);
        }
        t1->deallocate();
        t2->deallocate();
    }

    void test_filter_neg2() {
        // filter_by_negation
        relation_signature sig4;
        sig4.push_back(bv.mk_sort(1));
        sig4.push_back(bv.mk_sort(1));
        sig4.push_back(bv.mk_sort(1));
        unsigned_vector cols, allcols;

        cols.push_back(0);
        cols.push_back(2);
        allcols.push_back(0);
        allcols.push_back(1);
        allcols.push_back(2);

        /// xxx \ 1x0
        udoc_relation* t1 = mk_full(sig4);
        {
            udoc_relation* neg = mk_full(sig4);
            doc& n = neg->get_udoc()[0];
            neg->get_dm().set(n, 0, BIT_1);
            neg->get_dm().set(n, 2, BIT_0);
            apply_filter_neg(*t1, *neg, allcols, allcols);
            neg->deallocate();
        }

        /// xxx \ (1x1 u 0x0)
        udoc_relation* t2 = mk_full(sig4);
        {
            udoc_relation* neg = mk_full(sig4);
            doc& n = neg->get_udoc()[0];
            neg->get_dm().set(n, 0, BIT_0);
            neg->get_dm().set(n, 2, BIT_0);
            apply_filter_neg(*t2, *neg, allcols, allcols);
            neg->deallocate();
        }
        {
            udoc_relation* neg = mk_full(sig4);
            doc& n = neg->get_udoc()[0];
            neg->get_dm().set(n, 0, BIT_1);
            neg->get_dm().set(n, 2, BIT_1);
            apply_filter_neg(*t2, *neg, allcols, allcols);
            neg->deallocate();
        }
        t1->display(std::cout);
        t2->display(std::cout);

        apply_filter_neg(*t2, *t1, cols, cols);
        t1->deallocate();
        t2->deallocate();
    }

    void test_filter_neg3() {
        // filter_by_negation
        relation_signature sig;
        sig.push_back(bv.mk_sort(1));
        sig.push_back(bv.mk_sort(1));
        sig.push_back(bv.mk_sort(1));
        unsigned_vector cols1, cols2;

        cols1.push_back(0);
        cols1.push_back(0);
        cols2.push_back(0);
        cols2.push_back(1);

        /// 1xx
        udoc_relation* t1 = mk_full(sig);
        {
            doc& d = t1->get_udoc()[0];
            t1->get_dm().set(d, 0, BIT_1);
        }

        /// 10x
        udoc_relation* t2 = mk_full(sig);
        {
            doc& d = t2->get_udoc()[0];
            t1->get_dm().set(d, 0, BIT_1);
            t1->get_dm().set(d, 1, BIT_0);
        }

        apply_filter_neg(*t1, *t2, cols1, cols2);
        t1->deallocate();
        t2->deallocate();
    }

    void test_filter_neg4(bool disable_fast) {
        relation_signature sig1, sig2;
        sig1.push_back(bv.mk_sort(2));
        sig1.push_back(bv.mk_sort(2));
        sig2.push_back(bv.mk_sort(2));
        unsigned_vector cols1, cols2;

        cols1.push_back(0);
        cols1.push_back(1);
        cols2.push_back(0);
        cols2.push_back(0);
        udoc_relation* tgt = mk_full(sig1);
        udoc_relation* neg = mk_full(sig2);
        if (disable_fast) p.disable_fast_pass();
        apply_filter_neg(*tgt, *neg, cols1, cols2);
        tgt->deallocate();

        tgt = mk_full(sig1);
        apply_filter_neg(*neg, *tgt, cols2, cols1);
        tgt->deallocate();
        neg->deallocate();        
    }

    void test_filter_neg5(bool disable_fast) {
        relation_signature sig1, sig2;
        sig1.push_back(bv.mk_sort(2));
        sig1.push_back(bv.mk_sort(2));
        sig2.push_back(bv.mk_sort(2));
        sig2.push_back(bv.mk_sort(2));
        sig2.push_back(bv.mk_sort(2));
        unsigned_vector cols1, cols2, cols3;

        cols1.push_back(0);
        cols1.push_back(1);
        cols2.push_back(0);
        cols2.push_back(2);
        cols3.push_back(0);
        cols3.push_back(1);
        udoc_relation* tgt = mk_full(sig1);
        udoc_relation* neg = mk_full(sig2);
        rel_mut filter_id = p.mk_filter_identical_fn(*tgt, cols3.size(), cols3.data());
        (*filter_id)(*tgt);
        if (disable_fast) p.disable_fast_pass();
        apply_filter_neg(*tgt, *neg, cols1, cols2);
        tgt->deallocate();
        neg->deallocate();        
    }

    void set_random(udoc_relation& r, unsigned num_vals) {
        unsigned num_bits = r.get_dm().num_tbits();
        udoc_relation* full = mk_full(r.get_signature());
        rel_union union_fn = p.mk_union_fn(r, r, nullptr);
        (*union_fn)(r, *full);
        doc_manager& dm = r.get_dm();
        ENSURE(r.get_udoc().size() == 1);
        doc& d0 = r.get_udoc()[0];
        ENSURE(dm.is_full(d0));            
        for (unsigned i = 0; i < num_vals; ++i) {
            unsigned idx = m_rand(num_bits);
            unsigned val = m_rand(2);
            tbit b = (val == 0)?BIT_0:BIT_1;
            dm.set(d0, idx, b);
        }
        full->deallocate();
    }

    void apply_filter_neg(udoc_relation& dst, udoc_relation& neg, 
                          unsigned_vector const& cols1, unsigned_vector const& cols2) {

        scoped_ptr<datalog::relation_intersection_filter_fn> negf;
        negf = p.mk_filter_by_negation_fn(dst, neg, cols1.size(), cols1.data(), cols2.data());
        expr_ref dst0(m);
        dst.to_formula(dst0);
        (*negf)(dst, neg);
        cr.verify_filter_by_negation(dst0, dst, neg, cols1, cols2);

        /*
          
        tgt_1:={ x: x\in tgt_0 && ! \exists y: 
                    ( y \in neg & pi_c1(x)= pi_d1(y) & ... & pi_cN(x)= pi_dN(y) ) }
        */
    }

    expr_ref ex(unsigned hi, unsigned lo, expr* e) {
        expr_ref result(m);
        result = bv.mk_extract(hi, lo, e);
        return result;
    }

    void apply_filter_project(udoc_relation& t, unsigned_vector const& rm, app* cond) {
        scoped_ptr<datalog::relation_transformer_fn> rt;
        rt = p.mk_filter_interpreted_and_project_fn(t, cond, rm.size(), rm.data());
        datalog::relation_base* result = (*rt)(t);
        cr.verify_filter_project(t, *result, cond, rm);
        result->deallocate();
    }

    void project_var(unsigned i, sort* s, expr_ref& fml) {
        var_ref v(m);
        v = m.mk_var(i, s);
        unsigned num_bits = bv.get_bv_size(s);
        unsigned p = 1 << num_bits;
        expr_ref_vector disj(m);
        expr_ref tmp(m);
        for (unsigned i = 0; i < p; ++i) {
            expr_safe_replace repl(m);
            repl.insert(v, bv.mk_numeral(rational(i), s));
            tmp = fml;
            repl(tmp);
            disj.push_back(tmp);
        }
        fml = mk_or(m, disj.size(), disj.data());
    }

    void apply_filter(udoc_relation& t, app* cond) {
        udoc_relation* full = mk_full(t.get_signature());
        rel_union union_fn = p.mk_union_fn(t, *full, nullptr);
        (*union_fn)(t, *full, nullptr);
        expr_ref fml0(m);
        t.to_formula(fml0);
        rel_mut fint = p.mk_filter_interpreted_fn(t, cond);
        (*fint)(t);
        t.display(std::cout << "filter: " << mk_pp(cond, m) << " "); std::cout << "\n";
        cr.verify_filter(fml0, t, cond);
        full->deallocate();
    }


};

void tst_udoc_relation() {
    udoc_tester tester;

    try {
        tester.test1();
    }
    catch (z3_exception& ex) {
        std::cout << ex.msg() << "\n";
    }
}
