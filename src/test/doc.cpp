#include "doc.h"

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
    unsigned hi = 3, lo = 1;
    SASSERT(hi <= n);
    doc_ref d111X(m, m.allocate(0xFF, hi, lo));
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
    m.subtract(*d1,*d0, result);
    SASSERT(result.empty());
    SASSERT(m.contains(*dX,*d1));
    SASSERT(m.contains(*dX,*d0));
    SASSERT(!m.contains(*d0,*d1));
    SASSERT(!m.contains(*d1,*d0));


    d1->neg().push_back(m.tbvm().allocate0());
    m.display(std::cout, *d1) << " -> ";
    VERIFY(m.fold_neg(*d1));
    m.display(std::cout, *d1) << "\n";


    svector<bool> to_delete(n);
    to_delete[1] = true;
    to_delete[3] = true;
    doc_manager m1(n-2);
    doc_ref d1_1(m1, m1.project(n, to_delete.c_ptr(), *d0));
    doc_ref d1_2(m1, m1.allocate1());
    m.display(std::cout, *d1) << " -> ";
    m1.display(std::cout, *d1_1) << "\n";
    SASSERT(m1.equals(*d1_1,*d1_2));
    
}


// generate "all" clauses over num_vars
// create XXXX \ clauses
// project 0, 1, 2, 3 variables
// check that result is the same as QE over those clauses.

class test_doc_project {
    random_gen m_ran;

    void test_clauses(unsigned num_vars, unsigned num_clauses) {
        //
    }

public:    
    void operator()(unsigned num_vars, unsigned min_clauses, unsigned max_clauses) {        
        for (unsigned i = min_clauses; i < max_clauses; ++i) {
            test_clauses(num_vars, i);
        }    
    }
};

void tst_doc() {
    tst_doc1(5);
    tst_doc1(10);
    tst_doc1(70);
}
