#include "proof_checker.h"
#include "ast_ll_pp.h"

void tst_checker1() {
    ast_manager m(PGM_FINE);
    expr_ref a(m);
    proof_ref p1(m), p2(m), p3(m), p4(m);
    bool result;
    expr_ref_vector side_conditions(m);

    a = m.mk_const(symbol("a"), m.mk_bool_sort());
    p1 = m.mk_hypothesis(a.get());
    p2 = m.mk_hypothesis(m.mk_not(a.get()));
    ast_ll_pp(std::cout, m, p1.get());
    ast_ll_pp(std::cout, m, p2.get());
    proof* proofs[2] = { p1.get(), p2.get() };
    p3 = m.mk_unit_resolution(2, proofs);
    p4 = m.mk_lemma(p3.get(), a.get());
    ast_ll_pp(std::cout, m, p4.get());
    proof_checker checker(m);
    p4 = m.mk_lemma(p3.get(), m.mk_or(a.get(), m.mk_not(a.get())));
    ast_ll_pp(std::cout, m, p4.get());
    result = checker.check(p4.get(), side_conditions);
    SASSERT(result);    
}

void tst_proof_checker() {
    tst_checker1();    
}
