#include "udoc_relation.h"
#include "trace.h"
#include "vector.h"
#include "ast.h"
#include "ast_pp.h"
#include "reg_decl_plugins.h"
#include "sorting_network.h"
#include "smt_kernel.h"
#include "model_smt2_pp.h"
#include "smt_params.h"
#include "ast_util.h"
#include "expr_safe_replace.h"
#include "th_rewriter.h"
#include "dl_relation_manager.h"
#include "dl_register_engine.h"
#include "rel_context.h"
#include "bv_decl_plugin.h"


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
        t = mk_rand_tbv(dm);
        doc* result = dm.allocate(*t);
        SASSERT(dm.tbvm().equals(*t, result->pos()));
        for (unsigned i = 0; i < num_diff; ++i) {
            result->neg().push_back(mk_rand_tbv(dm, result->pos()));            
        }        
        SASSERT(dm.well_formed(*result));
        return result;
    }

    void mk_rand_udoc(doc_manager& dm, unsigned num_elems, unsigned num_diff, udoc& result) {
        result.reset(dm);
        for (unsigned i = 0; i < num_elems; ++i) {
            result.push_back(mk_rand_doc(dm, num_diff));
        }
    }

public:
    udoc_tester(): m_init(m), bv(m), m_vars(m), m_ctx(m, m_reg, m_smt_params), rc(m_ctx),
                   p(dynamic_cast<udoc_plugin&>(*rc.get_rmanager().get_relation_plugin(symbol("doc"))))
    {        
    }

    udoc_relation* mk_empty(relation_signature const& sig) {
        SASSERT(p.can_handle_signature(sig));
        relation_base* empty = p.mk_empty(sig);
        return dynamic_cast<udoc_relation*>(empty);
    }

    udoc_relation* mk_full(relation_signature const& sig) {
        func_decl_ref fn(m);
        fn = m.mk_func_decl(symbol("full"), sig.size(), sig.c_ptr(), m.mk_bool_sort());
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

        test_join(1000);

        test_rename();
        test_filter_neg();


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
            datalog::relation_join_fn* join_fn = p.mk_join_fn(*t1, *t2, jc1.size(), jc1.c_ptr(), jc2.c_ptr());
            SASSERT(join_fn);
            t = (*join_fn)(*t1, *t2);
            t->display(std::cout); std::cout << "\n";
            t->deallocate();

            t = (*join_fn)(*t1, *t3);
            SASSERT(t->empty());
            t->display(std::cout); std::cout << "\n";
            t->deallocate();

            t = (*join_fn)(*t3, *t3);
            SASSERT(t->empty());
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
            datalog::relation_transformer_fn* proj_fn = p.mk_project_fn(*t1, pc.size(), pc.c_ptr());
            t = (*proj_fn)(*t1);
            t->display(std::cout); std::cout << "\n";
            t->deallocate();
            
            t1->reset();
            t = (*proj_fn)(*t1);
            t->display(std::cout); std::cout << "\n";
            t->deallocate();
            
            t1->add_fact(fact1);
            t1->add_fact(fact2);
            t1->add_fact(fact3);
            t = (*proj_fn)(*t1);
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

            rel_union union_fn = p.mk_union_fn(*t1, *t2, 0);

            t1->display(std::cout << "t1 before:"); std::cout << "\n";
            (*union_fn)(*t1, *t2, delta);
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
            rel_mut filter_id = p.mk_filter_identical_fn(*t1, id.size(), id.c_ptr());
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
            for (unsigned i = 0; i < conds.size(); ++i) {
                apply_filter_project(*t1, remove, conds[i].get());
            }
            remove[1] = 1;
            for (unsigned i = 0; i < conds.size(); ++i) {
                apply_filter_project(*t1, remove, conds[i].get());
            }
            t1->deallocate();
        }


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

        join_fn = p.mk_join_fn(*t1, *t2, jc1.size(), jc1.c_ptr(), jc2.c_ptr());
        t = (*join_fn)(*t1, *t2);

        verify_join(*t1, *t2, *t, jc1.size(), jc1.c_ptr(), jc2.c_ptr());
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

    void verify_join(relation_base const& t1, relation_base& t2, relation_base& t,
                     unsigned sz, unsigned const* cols1, unsigned const* cols2) {
        relation_signature const& sig1 = t1.get_signature();
        relation_signature const& sig2 = t2.get_signature();
        relation_signature const& sig  = t.get_signature();
        expr_ref fml1(m), fml2(m), fml3(m);
        var_ref var1(m), var2(m);
        t1.to_formula(fml1);
        t2.to_formula(fml2);
        t.to_formula(fml3);
        var_subst sub(m, false);
        expr_ref_vector vars(m);
        for (unsigned i = 0; i < sig2.size(); ++i) {
            vars.push_back(m.mk_var(i + sig1.size(), sig2[i]));
        }
        sub(fml2, vars.size(), vars.c_ptr(), fml2);
        fml1 = m.mk_and(fml1, fml2);
        for (unsigned i = 0; i < sz; ++i) {
            unsigned v1 = cols1[i];
            unsigned v2 = cols2[i];
            var1 = m.mk_var(v1, sig1[v1]);
            var2 = m.mk_var(v2 + sig1.size(), sig2[v2]);
            fml1 = m.mk_and(m.mk_eq(var1, var2), fml1);
        }
        vars.reset();
        for (unsigned i = 0; i < sig.size(); ++i) {
            std::stringstream strm;
            strm << "x" << i;
            vars.push_back(m.mk_const(symbol(strm.str().c_str()), sig[i]));            
        }
        sub(fml1, vars.size(), vars.c_ptr(), fml1);
        sub(fml3, vars.size(), vars.c_ptr(), fml3);
        check_equiv(fml1, fml3);
    }
    
    

    void check_permutation(relation_base* t1, unsigned_vector const& cycle) {
        scoped_ptr<datalog::relation_transformer_fn> rename;
        rename = p.mk_rename_fn(*t1, cycle.size(), cycle.c_ptr());        
        relation_base* t = (*rename)(*t1);
        verify_permutation(*t1,*t, cycle);
        t1->display(std::cout); std::cout << "\n";
        t->display(std::cout); std::cout << "\n";
        t->deallocate();            
        t1->deallocate();
    }

    void verify_permutation(relation_base const& src, relation_base const& dst, 
                            unsigned_vector const& cycle) {
        unsigned_vector perm;
        relation_signature const& sig1 = src.get_signature();
        relation_signature const& sig2 = dst.get_signature();
        for (unsigned i = 0; i < sig1.size(); ++i) {
            perm.push_back(i);
        }
        for (unsigned i = 0; i < cycle.size(); ++i) {
            unsigned j = (i + 1)%cycle.size();
            unsigned col1 = cycle[i];
            unsigned col2 = cycle[j];
            perm[col2] = col1;
        }
        for (unsigned i = 0; i < perm.size(); ++i) {
            SASSERT(sig2[perm[i]] == sig1[i]);
        }
        expr_ref_vector sub(m);
        for (unsigned i = 0; i < perm.size(); ++i) {
            sub.push_back(m.mk_var(perm[i], sig1[i]));
        }
        var_subst subst(m, false);
        expr_ref fml1(m), fml2(m);
        src.to_formula(fml1);
        dst.to_formula(fml2);
        subst(fml1, sub.size(), sub.c_ptr(), fml1);
        expr_ref_vector vars(m);
        for (unsigned i = 0; i < sig2.size(); ++i) {
            std::stringstream strm;
            strm << "x" << i;
            vars.push_back(m.mk_const(symbol(strm.str().c_str()), sig2[i]));            
        }

        subst(fml1, vars.size(), vars.c_ptr(), fml1);
        subst(fml2, vars.size(), vars.c_ptr(), fml2);
        
        check_equiv(fml1, fml2);
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

    void set_random(udoc_relation& r, unsigned num_vals) {
        unsigned num_bits = r.get_dm().num_tbits();
        udoc_relation* full = mk_full(r.get_signature());
        rel_union union_fn = p.mk_union_fn(r, r, 0);
        (*union_fn)(r, *full);
        doc_manager& dm = r.get_dm();
        SASSERT(r.get_udoc().size() == 1);
        doc& d0 = r.get_udoc()[0];
        SASSERT(dm.is_full(d0));            
        for (unsigned i = 0; i < num_vals; ++i) {
            unsigned idx = m_rand(num_bits);
            unsigned val = m_rand(2);
            tbit b = (val == 0)?BIT_0:BIT_1;
            dm.set(d0, idx, b);
        }
        full->deallocate();
    }

    void apply_filter_neg(udoc_relation& t1, udoc_relation& t2, 
                          unsigned_vector const& cols1, unsigned_vector const& cols2) {

        relation_signature const& sig = t1.get_signature();
        scoped_ptr<datalog::relation_intersection_filter_fn> negf;
        negf = p.mk_filter_by_negation_fn(t1, t2, cols1.size(), cols1.c_ptr(), cols2.c_ptr());
        expr_ref fml1(m), fml2(m), fml3(m);
        t1.to_formula(fml1);
        t2.to_formula(fml2);
        for (unsigned i = 0; i < cols1.size(); ++i) {
            std::cout << cols1[i] << " = " << cols2[i] << " ";
        }
        std::cout << "\n";
        t1.display(std::cout); std::cout << "\n";
        t2.display(std::cout); std::cout << "\n";
        (*negf)(t1, t2);
        t1.display(std::cout); std::cout << "\n";
        t1.to_formula(fml3);
        std::cout << fml1 << "\n";
        std::cout << fml2 << "\n";
        std::cout << fml3 << "\n";
        expr_ref_vector eqs(m);
        expr_ref_vector sub(m);
        for (unsigned i = 0; i < sig.size(); ++i) {
            sub.push_back(m.mk_var(i+sig.size(),sig[i]));
        }
        var_subst subst(m, false);
        subst(fml2, sub.size(), sub.c_ptr(), fml2);
        eqs.push_back(fml2);
        for (unsigned i = 0; i < cols1.size(); ++i) {
            var_ref v1(m), v2(m);
            unsigned c1 = cols1[i];
            unsigned c2 = cols2[i];
            v1 = m.mk_var(c1, sig[c1]);
            v2 = m.mk_var(sig.size() + c2, sig[c2]);
            eqs.push_back(m.mk_eq(v1,v2));
        }
        fml2 = mk_and(m, eqs.size(), eqs.c_ptr());
        for (unsigned i = 0; i < sub.size(); ++i) {
            project_var(sig.size() + i, m.get_sort(sub[i].get()), fml2);
        }
        fml1 = m.mk_and(fml1, m.mk_not(fml2));
        
        expr_ref_vector vars(m);
        for (unsigned i = 0; i < sig.size(); ++i) {
            std::stringstream strm;
            strm << "x" << i;
            vars.push_back(m.mk_const(symbol(strm.str().c_str()), sig[i]));            
        }

        subst(fml1, vars.size(), vars.c_ptr(), fml1);
        subst(fml3, vars.size(), vars.c_ptr(), fml3);

        check_equiv(fml1, fml3);
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
        rt = p.mk_filter_interpreted_and_project_fn(t, cond, rm.size(), rm.c_ptr());
        udoc_relation* full = mk_full(t.get_signature());
        rel_union union_fn = p.mk_union_fn(t, *full, 0);
        (*union_fn)(t, *full, 0);
        datalog::relation_base* result = (*rt)(t);
        
        for (unsigned i = 0; i < rm.size(); ++i) {
            std::cout << rm[i] << " ";
        }
        std::cout << mk_pp(cond, m) << "\n";
        t.display(std::cout);
        result->display(std::cout);
        result->deallocate();
        full->deallocate();
    }

    void verify_filter_project(udoc_relation const& r, unsigned_vector const& rm, app* cond) {
        expr_ref fml(m), cfml(m);
        r.to_formula(fml);
        cfml = cond;
        relation_signature const& sig = r.get_signature();
        expr_ref_vector vars(m);
        for (unsigned i = 0, j = 0, k = 0; i < sig.size(); ++i) {
            if (j < rm.size() && rm[j] == i) {
                project_var(i, sig[i], cfml);
                ++j;
            }
            else {
                vars.push_back(m.mk_var(k, sig[i]));
                ++k;
            }            
        }
        
        check_equiv(fml, cfml);
    }

    void check_equiv(expr* fml1, expr* fml2) {
        TRACE("doc", tout << mk_pp(fml1, m) << "\n";
              tout << mk_pp(fml2, m) << "\n";);
        smt_params fp;
        smt::kernel solver(m, fp);
        expr_ref tmp(m);
        tmp = m.mk_not(m.mk_eq(fml1, fml2));
        solver.assert_expr(tmp);
        lbool res = solver.check();
        SASSERT(res == l_false);
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
        fml = mk_or(m, disj.size(), disj.c_ptr());
    }

    void apply_filter(udoc_relation& t, app* cond) {
        udoc_relation* full = mk_full(t.get_signature());
        rel_union union_fn = p.mk_union_fn(t, *full, 0);
        (*union_fn)(t, *full, 0);
        rel_mut fint = p.mk_filter_interpreted_fn(t, cond);
        (*fint)(t);
        t.display(std::cout << "filter: " << mk_pp(cond, m) << " "); std::cout << "\n";
        verify_filter(t, cond);
        full->deallocate();
    }

    void verify_filter(udoc_relation& r, expr* fml2) {
        expr_ref fml1(m), tmp(m);
        r.to_formula(fml1);
        tmp = m.mk_not(m.mk_eq(fml1, fml2));
        relation_signature const& sig = r.get_signature();
        expr_ref_vector vars(m);
        var_subst sub(m, false);
        for (unsigned i = 0; i < sig.size(); ++i) {
            std::stringstream strm;
            strm << "x" << i;
            vars.push_back(m.mk_const(symbol(strm.str().c_str()), sig[i]));            
        }

        sub(tmp, vars.size(), vars.c_ptr(), tmp);
        
        smt_params fp;
        smt::kernel solver(m, fp);
        TRACE("doc", 
              tout << "Original formula:\n";
              tout << mk_pp(fml2, m) << "\n";
              tout << "Filtered formula: \n";
              tout << mk_pp(fml1,m) << "\n";
              tout << tmp << "\n";
              );
        solver.assert_expr(tmp);
        lbool res = solver.check();
        SASSERT(res == l_false);
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
