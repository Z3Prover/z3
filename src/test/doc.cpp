
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "doc.h"
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


static void tst_doc1(unsigned n) {
    doc_manager m(n);
    
    doc_ref d(m, m.allocate());
    doc_ref d1(m, m.allocate1());
    doc_ref d0(m, m.allocate0());
    doc_ref dX(m, m.allocateX());
    doc_ref dXc(m, m.allocate(*dX));
    doc_ref d10(m, m.allocate(10));
    doc_ref d20(m, m.allocate(rational(20)));
    m.display(std::cout, *d1) << "\n";
    m.display(std::cout, *d0) << "\n";
    m.display(std::cout, *dX) << "\n";
    m.display(std::cout, *d10) << "\n";
    m.display(std::cout, *d20) << "\n";
    if (n < 64) {
        unsigned hi = 3, lo = 1;
        SASSERT(hi <= n);
        doc_ref d111X(m, m.allocate(0xFF, hi, lo));
    }
    m.copy(*d, *d10);
    SASSERT(m.equals(*d, *d10));
    m.reset(*d);
    SASSERT(!m.equals(*d, *d10));
    m.fill0(*d10);
    SASSERT(m.equals(*d, *d10));
    m.fill1(*d);
    d10 = m.allocate(10);
    SASSERT(!m.equals(*d, *d10));
    SASSERT(m.equals(*d, *d1));
    m.fillX(*d);
    SASSERT(m.equals(*d, *dX));
    SASSERT(m.is_full(*dX));
    SASSERT(!m.is_full(*d1));

    VERIFY(m.set_and(*dX,*dX));
    SASSERT(m.equals(*dXc,*dX));
    VERIFY(m.set_and(*dX,*d1));
    SASSERT(!m.equals(*dXc,*dX));
    SASSERT(m.equals(*dX,*d1));
    VERIFY(m.fold_neg(*dX));
    ptr_vector<doc> result;
    //    VERIFY(!m.intersect(*d1,*d0, result));    
    //    m.subtract(*d1,*d0, result);
    SASSERT(result.empty());
    dX = m.allocateX();
    m.display(std::cout, *d0) << "\n";
    m.display(std::cout, *dX) << "\n";
    SASSERT(m.contains(*dX,*d1));
    SASSERT(m.contains(*dX,*d0));
    SASSERT(!m.contains(*d0,*d1));
    SASSERT(!m.contains(*d1,*d0));


    d1->neg().push_back(m.tbvm().allocate0());
    m.display(std::cout, *d1) << " -> ";
    VERIFY(m.fold_neg(*d1));
    m.display(std::cout, *d1) << "\n";


    bit_vector to_delete;
    to_delete.resize(n, false);
    to_delete.set(1);
    to_delete.set(3);
    doc_manager m1(n-2);
    doc_ref d1_1(m1, m.project(m1, to_delete, *d1));
    doc_ref d1_2(m1, m1.allocate1());
    m.display(std::cout, *d1) << " -> ";
    m1.display(std::cout, *d1_1) << "\n";
    SASSERT(m1.equals(*d1_1,*d1_2));
    m.set(*d1,2,BIT_x);
    m.set(*d1,4,BIT_x);
    d1_1 = m.project(m1, to_delete, *d1);
    m.display(std::cout, *d1) << " -> ";
    m1.display(std::cout, *d1_1) << "\n";
    d1->neg().push_back(m.tbvm().allocate1());
    SASSERT(m.well_formed(*d1));
    d1_1 = m.project(m1, to_delete, *d1);
    m.display(std::cout, *d1) << " -> ";
    m1.display(std::cout, *d1_1) << "\n";    
}


// generate "all" clauses over num_vars
// create XXXX \ clauses
// project 0, 1, 2, 3 variables
// check that result is the same as QE over those clauses.

class test_doc_cls {
    random_gen      m_ran;
    ast_manager     m;
    doc_manager     dm;
    expr_ref_vector m_vars;

    tbit choose_tbit() {
        switch (m_ran(3)) {
        case 0: return BIT_0;
        case 1: return BIT_1;
        default : return BIT_x;
        }
    }

    tbv* mk_rand_tbv() {
        tbv* result = dm.tbvm().allocate();
        for (unsigned i = 0; i < dm.num_tbits(); ++i) {
            dm.tbvm().set(*result, i, choose_tbit());
        }
        return result;
    }

    tbv* mk_rand_tbv(tbv const& pos) {
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
    
    doc* mk_rand_doc(unsigned num_diff) {
        tbv_ref t(dm.tbvm());
        t = mk_rand_tbv();
        doc* result = dm.allocate(*t);
        SASSERT(dm.tbvm().equals(*t, result->pos()));
        for (unsigned i = 0; i < num_diff; ++i) {
            result->neg().push_back(mk_rand_tbv(result->pos()));            
        }        
        SASSERT(dm.well_formed(*result));
        return result;
    }

    void mk_rand_udoc(unsigned num_elems, unsigned num_diff, udoc& result) {
        result.reset(dm);
        for (unsigned i = 0; i < num_elems; ++i) {
            result.push_back(mk_rand_doc(num_diff));
        }
    }

    expr_ref mk_conj(tbv& t) {
        expr_ref result(m);
        expr_ref_vector conjs(m);
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            tbit b = choose_tbit();
            dm.tbvm().set(t, i, b);            
            switch (b) {
            case BIT_1: conjs.push_back(m_vars[i].get()); break;
            case BIT_0: conjs.push_back(m.mk_not(m_vars[i].get())); break;
            default: break;
            }
        }
        result = mk_and(m, conjs.size(), conjs.c_ptr());
        return result;
    }

    expr_ref to_formula(tbv const& t, doc_manager& m2) {
        expr_ref result(m);
        expr_ref_vector conjs(m);
        unsigned n = m2.num_tbits();
        tbv_manager& tm = m2.tbvm();
        SASSERT(n <= m_vars.size());
        for (unsigned i = 0; i < n; ++i) {
            switch (t[i]) {
            case BIT_x:
                break;
            case BIT_1:
                conjs.push_back(m_vars[i].get());
                break;
            case BIT_0:
                conjs.push_back(m.mk_not(m_vars[i].get()));
                break;
            default:
                UNREACHABLE();
                break;
            }
        }
        result = mk_and(m, conjs.size(), conjs.c_ptr());
        return result;
    }

    expr_ref to_formula(doc const& d, doc_manager& m2) {
        expr_ref result(m);
        expr_ref_vector conjs(m);
        conjs.push_back(to_formula(d.pos(), m2));
        for (unsigned i = 0; i < d.neg().size(); ++i) {
            conjs.push_back(m.mk_not(to_formula(d.neg()[i], m2)));
        }
        result = mk_and(m, conjs.size(), conjs.c_ptr());
        return result;
    }

    expr_ref to_formula(udoc const& ud, doc_manager& m2) {
        expr_ref result(m);
        expr_ref_vector disjs(m);
        for (unsigned i = 0; i < ud.size(); ++i) {
            disjs.push_back(to_formula(ud[i], m2));
        }
        result = mk_or(m, disjs.size(), disjs.c_ptr());
        return result;
    }

    void project(doc const& d, doc_manager& m2, const bit_vector& to_delete, doc_ref& result) {
        result = dm.project(m2, to_delete, d);
        TRACE("doc",
              for (unsigned i = 0; i < m_vars.size(); ++i) {
                  tout << (to_delete.get(i)?"0":"1");
              }
              tout << " ";
              dm.display(tout, d) << " -> ";
              m2.display(tout, *result) << "\n";
              );        
    } 


    void test_project(unsigned num_clauses) {
        doc_ref d(dm);
        d = mk_rand_doc(3);
        expr_ref fml1(m), fml2(m), fml3(m), tmp1(m), tmp2(m), fml(m);
        fml1 = to_formula(*d, dm);
        bit_vector to_delete;
        to_delete.reserve(m_vars.size(), false);
        unsigned num_bits = 1;
        for (unsigned i = 1; i < to_delete.size(); ++i) {
            to_delete.set(i, m_ran(2) == 0);
            if (!to_delete.get(i)) ++num_bits;
        }
        doc_manager m2(num_bits);
        doc_ref result(m2);
        project(*d, m2, to_delete, result);
        TRACE("doc",              
              dm.display(tout, *d) << "\n";
              m2.display(tout, *result) << "\n";);
        fml2 = to_formula(*result, m2);
        project_expand(fml1, to_delete);
        project_rename(fml2, to_delete);
        check_equiv(fml1, fml2);
    }

    void project_expand(expr_ref& fml, bit_vector const& to_delete) {
        expr_ref tmp1(m), tmp2(m);
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            if (to_delete.get(i)) {
                expr_safe_replace rep1(m), rep2(m);
                rep1.insert(m_vars[i].get(), m.mk_true());
                rep1(fml, tmp1);
                rep2.insert(m_vars[i].get(), m.mk_false());
                rep2(fml, tmp2);
                if (tmp1 == tmp2) {
                    fml = tmp1;
                }
                else {
                    fml = m.mk_or(tmp1, tmp2);
                }
            }
        }
    }

    void project_rename(expr_ref& fml, bit_vector const& to_delete) {
        expr_safe_replace rep(m);
        for (unsigned i = 0, j = 0; i < m_vars.size(); ++i) {
            if (!to_delete.get(i)) {
                rep.insert(m_vars[j].get(), m_vars[i].get());
                ++j;
            }
        }
        rep(fml);
    }

    void test_merge(unsigned num_clauses) {
        doc_ref d(dm, dm.allocateX());
        expr_ref_vector fmls(m), eqs(m);
        unsigned N = m_vars.size();
        expr_ref fml1(m), fml2(m), fml3(m), tmp1(m), tmp2(m), fml(m);
        for (unsigned i = 0; i < num_clauses; ++i) {
            tbv* t = dm.tbvm().allocate();
            fmls.push_back(m.mk_not(mk_conj(*t)));
            d->neg().push_back(t);
        }
        fml1 = mk_and(m, fmls.size(), fmls.c_ptr());
        svector<bool> to_merge(N, false);
        bit_vector discard_cols;
        discard_cols.resize(N, false);
        unsigned num_bits = 1;
        union_find_default_ctx union_ctx;
        subset_ints equalities(union_ctx);
        unsigned lo = N;
        equalities.mk_var();
        for (unsigned i = 1; i < N; ++i) {
            to_merge[i] = (m_ran(2) == 0);
            if (!to_merge[i]) ++num_bits; else lo = i;
            equalities.mk_var();
        }
        if (lo == N) return;
        for (unsigned i = 0; i < N; ++i) {
            if (to_merge[i] && i != lo) {
                equalities.merge(i, lo);
                eqs.push_back(m.mk_eq(m_vars[i].get(), m_vars[lo].get()));
            }
        }
        eqs.push_back(to_formula(*d, dm));
        fml1 = mk_and(m, eqs.size(), eqs.c_ptr());
        if (dm.merge(*d, lo, 1, equalities, discard_cols)) {
            fml2 = to_formula(*d, dm);
        }
        else {
            fml2 = m.mk_false();
        }
        check_equiv(fml1, fml2);
    }

    void check_equiv(expr_ref& fml1, expr_ref& fml2) {
        th_rewriter rw(m);
        rw(fml1);
        rw(fml2);
        smt_params fp;
        smt::kernel solver(m, fp);
        expr_ref fml(m);
        fml = m.mk_not(m.mk_eq(fml1, fml2));
        solver.assert_expr(fml);
        lbool res = solver.check();
        if (res != l_false) {
            TRACE("doc",
                  tout << mk_pp(fml1, m) << "\n";
                  tout << mk_pp(fml2, m) << "\n";
                  );
        }
        SASSERT(res == l_false);
    }


public:    
    test_doc_cls(unsigned num_vars): dm(num_vars), m_vars(m) {
        reg_decl_plugins(m);
        for (unsigned i = 0; i < num_vars; ++i) {
            m_vars.push_back(m.mk_fresh_const("b", m.mk_bool_sort()));
        }
    }

    void test_project(unsigned num_rounds, unsigned num_clauses) {        
        for (unsigned i = 0; i < num_rounds; ++i) {
            test_project(num_clauses);
        }    
    }

    void test_merge(unsigned num_rounds, unsigned num_clauses) {
        for (unsigned i = 0; i < num_rounds; ++i) {
            test_merge(num_clauses);
        }    
    }

    void test_project1() {
        expr_ref fml1(m), fml2(m);
        doc_ref d(dm, dm.allocateX());
        tbv_ref t(dm.tbvm(), dm.tbvm().allocateX());
        dm.tbvm().set(*t, 0, BIT_0);
        d->neg().push_back(t.detach());
        unsigned num_bits = dm.num_tbits();
        bit_vector to_delete;
        to_delete.reserve(num_bits, false);
        fml1 = to_formula(*d, dm);
        to_delete.set(0, true);
        doc_manager m2(num_bits-1);
        doc_ref result(m2);
        project(*d, m2, to_delete, result);
        dm.display(std::cout, *d) << "\n";
        m2.display(std::cout, *result) << "\n";
        fml2 = to_formula(*result, m2);
        project_rename(fml2, to_delete);
        project_expand(fml1, to_delete);
        std::cout << fml1 << " " << fml2 << "\n";
        check_equiv(fml1, fml2);
    }


    void test_subtract() {
        doc_ref d1(dm);
        doc_ref d2(dm);
        doc_ref d3(dm);
        udoc ds1, ds2;
        d1 = dm.allocateX();
        d2 = dm.allocateX();
        d3 = dm.allocateX();
        dm.set(*d1, 0, BIT_1);
        dm.set(*d1, 1, BIT_0);
        dm.set(*d2, 0, BIT_0);
        dm.set(*d2, 1, BIT_1);
        //ds1.push_back(d1.detach());
        ds1.push_back(d2.detach());
        // ds1 = {10x, 01x}
        d1 = dm.allocateX();
        tbv_ref t1(dm.tbvm());
        tbv_ref t2(dm.tbvm());
        t1 = dm.tbvm().allocateX();
        t2 = dm.tbvm().allocateX();
        dm.tbvm().set(*t1, 0, BIT_1);
        dm.tbvm().set(*t1, 2, BIT_0);
        dm.tbvm().set(*t2, 0, BIT_0);
        dm.tbvm().set(*t2, 2, BIT_1);
        d1->neg().push_back(t1.detach());
        d1->neg().push_back(t2.detach());
        ds2.push_back(d1.detach());
        ds1.display(dm, std::cout) << "\n";
        ds2.display(dm, std::cout) << "\n";
        expr_ref fml1 = to_formula(ds1, dm);
        expr_ref fml2 = to_formula(ds2, dm);
        ds1.subtract(dm, ds2);
        ds1.display(dm, std::cout) << "\n";
        expr_ref fml3 = to_formula(ds1, dm);
        fml1 = m.mk_and(fml1, m.mk_not(fml2));
        check_equiv(fml1, fml3);       
        ds1.reset(dm);
        ds2.reset(dm);
        //sub:{xxx \ {1x0, 0x1}}
        //result:{100}

        for (unsigned i = 0; i < 1000; ++i) {
            udoc d1, d2;
            mk_rand_udoc(3, 3, d1);
            mk_rand_udoc(3, 3, d2);
            fml1 = to_formula(d1, dm);
            fml2 = to_formula(d2, dm);
            d1.subtract(dm, d2);
            fml3 = to_formula(d1, dm);
            fml1 = m.mk_and(fml1, m.mk_not(fml2));
            check_equiv(fml1, fml3);
            d1.reset(dm);
            d2.reset(dm);
        }
    }

    void test_intersect() {
        expr_ref fml1(m), fml2(m), fml3(m);
        for (unsigned i = 0; i < 10000; ++i) {
            udoc d1, d2;
            mk_rand_udoc(3, 3, d1);
            mk_rand_udoc(3, 3, d2);
            fml1 = to_formula(d1, dm);
            fml2 = to_formula(d2, dm);
            TRACE("doc", 
                  d1.display(dm, tout) << "\n";
                  d2.display(dm, tout) << "\n";);
            d1.intersect(dm, d2);
            TRACE("doc", d1.display(dm, tout) << "\n";);
            SASSERT(d1.well_formed(dm));
            fml3 = to_formula(d1, dm);
            fml1 = m.mk_and(fml1, fml2);
            check_equiv(fml1, fml3);
            d1.reset(dm);
            d2.reset(dm);
        }
    }

};


void tst_doc() {

    test_doc_cls tp(4);
    tp.test_project1();
    tp.test_project(200,7);

    tp.test_intersect();
    tp.test_subtract();
    tp.test_merge(200,7);

    tst_doc1(5);
    tst_doc1(10);
    tst_doc1(70);
}
