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


static void tst_doc1(unsigned n) {
    doc_manager m(n);
    
    m.allocate();
    m.reset();

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


    svector<bool> to_delete(n, false);
    to_delete[1] = true;
    to_delete[3] = true;
    doc_manager m1(n-2);
    doc_ref d1_1(m1, m.project(m1, n, to_delete.c_ptr(), *d1));
    doc_ref d1_2(m1, m1.allocate1());
    m.display(std::cout, *d1) << " -> ";
    m1.display(std::cout, *d1_1) << "\n";
    SASSERT(m1.equals(*d1_1,*d1_2));
    m.set(*d1,2,BIT_x);
    m.set(*d1,4,BIT_x);
    d1_1 = m.project(m1, n, to_delete.c_ptr(), *d1);
    m.display(std::cout, *d1) << " -> ";
    m1.display(std::cout, *d1_1) << "\n";
    d1->neg().push_back(m.tbvm().allocate1());
    SASSERT(m.well_formed(*d1));
    d1_1 = m.project(m1, n, to_delete.c_ptr(), *d1);
    m.display(std::cout, *d1) << " -> ";
    m1.display(std::cout, *d1_1) << "\n";    
}


// generate "all" clauses over num_vars
// create XXXX \ clauses
// project 0, 1, 2, 3 variables
// check that result is the same as QE over those clauses.

class test_doc_project {
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
    void mk_clause(expr_ref& result, tbv& t) {
        expr_ref_vector clause(m);
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            tbit b = choose_tbit();
            t.set(i, b);            
            switch (b) {
            case BIT_0: clause.push_back(m.mk_not(m_vars[i].get())); break;
            case BIT_1: clause.push_back(m_vars[i].get()); break;
            default: break;
            }
        }
        result = mk_or(m, clause.size(), clause.c_ptr());
    }

    void project(doc const& d, doc_manager& m2, bool const* to_delete) {
        doc_ref result(m2);
        dm.display(std::cout, d) << " -> ";
        result = dm.project(m2, m_vars.size(), to_delete, d);
        m2.display(std::cout, *result) << "\n";
    } 

    void test_clauses(unsigned num_clauses) {
        doc_ref d(dm, dm.allocateX());
        expr_ref_vector fmls(m);
        expr_ref fml(m);
        for (unsigned i = 0; i < num_clauses; ++i) {
            expr_ref clause(m);
            tbv* t = dm.tbvm().allocate();
            mk_clause(clause, *t);
            d->neg().push_back(t);
            fmls.push_back(clause);
        }
        fml = mk_and(m, fmls.size(), fmls.c_ptr());
        svector<bool> to_delete(m_vars.size(), false);
        unsigned num_bits = 1;
        for (unsigned i = 1; i < to_delete.size(); ++i) {
            to_delete[i] = (m_ran(2) == 0);
            if (!to_delete[i]) ++num_bits;
        }
        doc_manager m2(num_bits);
        project(*d, m2, to_delete.c_ptr());
        // std::cout << fml << "\n";
        //
    }

public:    
    test_doc_project(unsigned num_vars): dm(num_vars), m_vars(m) {
        reg_decl_plugins(m);
        for (unsigned i = 0; i < num_vars; ++i) {
            m_vars.push_back(m.mk_fresh_const("b", m.mk_bool_sort()));
        }
    }

    void operator()(unsigned num_rounds, unsigned num_clauses) {        
        for (unsigned i = 0; i < num_rounds; ++i) {
            test_clauses(num_clauses);
        }    
    }
};

void tst_doc() {
    tst_doc1(5);
    tst_doc1(10);
    tst_doc1(70);

    test_doc_project tp(4);    
    tp(5,7);
}
