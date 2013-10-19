#include "ast.h"
#include "smt_params.h"
#include "simplifier.h"
#include "qe.h"
#include "basic_simplifier_plugin.h"
#include "arith_simplifier_plugin.h"
#include "array_simplifier_plugin.h"
#include "bv_simplifier_plugin.h"
#include "ast_pp.h"
#include "smtlib.h"
#include "smtparser.h"
#include "lbool.h"
#include <sstream>
#include "reg_decl_plugins.h"


static void test_qe(ast_manager& m, lbool expected_outcome, expr* fml, char const* option) {

    //    enable_trace("bit2int");
    //enable_trace("gomory_cut");
    enable_trace("final_check_arith");
    enable_trace("arith_final_check");
    //enable_trace("arith_branching");
    enable_trace("theory_arith_int");
    enable_trace("presburger");
    enable_trace("quant_elim");
    // enable_trace("arith_simplifier_plugin");
    // enable_trace("non_linear");
    // enable_trace("gomory_cut_detail");
    // enable_trace("arith");
    // enable_trace("bv");
    // enable_trace("after_search");
    // enable_trace("bv_bit_prop");

    simplifier simp(m);
    smt_params params;
    // params.m_quant_elim = true;

    std::cout << mk_pp(fml, m) << "\n";
    qe::expr_quant_elim qe(m, params);
    expr_ref result(m);
    qe(m.mk_true(), fml, result);
    std::cout << " -> " << mk_pp(result, m) << " " << expected_outcome << "\n";
    if (expected_outcome == l_true && !m.is_true(result)) {
        std::cout << "ERROR: expected true, instead got " << mk_pp(result, m) << "\n";
        //exit(-1);
    }
    if (expected_outcome == l_false && !m.is_false(result)) {
        std::cout << "ERROR: expected false, instead got " << mk_pp(result, m) << "\n";
        //exit(-1);
    }
}

static void test_formula(lbool expected_outcome, char const* fml) {
    ast_manager m;
    reg_decl_plugins(m);
    scoped_ptr<smtlib::parser> parser = smtlib::parser::create(m);
    parser->initialize_smtlib();

    std::ostringstream buffer;
    buffer << "(benchmark presburger :status unknown :logic AUFLIA :extrapreds ((p1) (p2) (p3)) "
           << ":extrafuns ((a Int) (b Int))\n"
           << ":extrapreds ((p) (q) (r))\n"
           << ":datatypes ((list (nil) (cons (hd Int) (tl list))))\n"
           << ":datatypes ((cell (cnil) (ccons (car cell) (cdr cell))))\n"
           << ":extrasorts (U)\n"
           << ":extrafuns ((f U U))\n"
           << ":formula " << fml << ")";
    parser->parse_string(buffer.str().c_str());
    smtlib::benchmark* b = parser->get_benchmark();
    smtlib::theory::expr_iterator it  = b->begin_formulas();
    smtlib::theory::expr_iterator end = b->end_formulas();
    for (; it != end; ++it) {
        test_qe(m, expected_outcome, *it, 0);
    }
}

void tst_quant_elim() {
    disable_debug("heap");

    test_formula(l_undef, "(exists ((p1 Bool) (q1 Bool) (r1 Bool))\
                                    (and (or (not p1) (not q1) r1)\
                                         (or (and (not p) (not q) (not p1) q1)\
                                             (and (not p) q p1 (not q1))\
                                             (and p (not q) p1 q1)\
                                             (and p q p1 q1))\
                                         (or (and (not r) (not r1))\
                                             (and (= p p1) (= q q1) r r1)\
                                             (and (not (and (= p p1) (= q q1))) (not (= r r1))))))");


    test_formula(l_false,"(forall (x Int) (y Int) (or (= x 0) (< (* 5 y) (* 6 x)) (> (* 5 y) (* 6 x))))");

    test_formula(l_false, "(forall (a Int) (b Int) (exists (x Int) (and (< a (* 20 x)) (< (* 20 x) b))))");

    test_formula(l_undef, "(exists (u U) (= (f u) u))");

    test_formula(l_true, 
                 "(exists (l Int) (forall (x Int) (implies (>= x l) "
                 "       (exists (u Int) (v Int) (and (>= u 0) (>= v 0) (= x (+ (* 3 u) (* 7 v))))))))");


    test_formula(l_true, "(forall (x Int) (y Int) (implies (= (* 6 x) (* 5 y)) (exists (d Int) (= y (* 3 d)))))");

    test_formula(l_undef,  "(exists (x Int) (= (- a (mod x 4)) 0))");
    // return;


    //    test_formula(l_true, "(exists (x Int) (y Int) (= 1 (+ (* 5 x) (* 3 y))))");


    test_formula(l_undef, "(exists (a Bool) (b Bool) (or (and p1 a) (and p2 (not b))))");




    test_formula(l_false, 
                 "(forall (x Int) (q1 Int) (q2 Int) (r1 Int) (r2 Int) "
                 "  (implies "
                 "    (and (< x 4699) "
                 "         (= (* 2622 x) (+ (* 65536 q1) r1)) "
                 "         (<= 0 q1) "
                 "         (<= 0 r1) "
                 "         (< r1 65536) "
                 "         (= x (+ (* 100 q2) r2)) "
                 "         (<= 0 q2) "
                 "         (<= 0 r2) "
                 "         (< r2 100)) "
                 "         (= q1 q2)))");



    test_formula(l_undef, 
                 "(forall (l list) (or (= l nil) (exists (x Int) (ll list) (= l (cons x ll)))))");






    test_formula(l_false, "(exists (x Real) (forall (y Real) (>= x y)))");
    test_formula(l_false, "(exists (x Real) (forall (y Real) (> x y)))");
    test_formula(l_false, "(exists (x Real) (forall (y Real) (< x y)))");
    test_formula(l_false, "(exists (x Real) (forall (y Real) (<= x y)))");

    test_formula(l_true, "(exists (x Real) (exists (y Real) (< x y)))");
    test_formula(l_true, "(exists (x Real) (exists (y Real) (<= x y)))");
    test_formula(l_true, "(exists (x Real) (exists (y Real) (>= x y)))");
    test_formula(l_true, "(exists (x Real) (exists (y Real) (> x y)))");

    test_formula(l_true, "(forall (x Real) (exists (y Real) (< x y)))");
    test_formula(l_true, "(forall (x Real) (exists (y Real) (<= x y)))");
    test_formula(l_true, "(forall (x Real) (exists (y Real) (>= x y)))");
    test_formula(l_true, "(forall (x Real) (exists (y Real) (> x y)))");

    test_formula(l_false, "(forall (x Real) (forall (y Real) (< x y)))");
    test_formula(l_false, "(forall (x Real) (forall (y Real) (<= x y)))");
    test_formula(l_false, "(forall (x Real) (forall (y Real) (>= x y)))");
    test_formula(l_false, "(forall (x Real) (forall (y Real) (> x y)))");





    test_formula(l_true, 
                 "(exists (l Int) (forall (x Int) (implies (>= x l) "
                 "       (exists (u Int) (v Int) (and (>= u 0) (>= v 0) (= x (+ (* 3 u) (* 5 v))))))))");


    test_formula(l_false, "(forall (d Int) (implies (>= d 0) (exists (x Int) (y Int) (and (>= x 0) (>= y 0) (= d (+ (* 3 x) (* 5 y)))))))");

    test_formula(l_true, "(forall (y Int) (implies (exists (d Int) (= y (* 6 d))) (exists (d Int) (= y (* 2 d)))))");

    test_formula(l_true, "(forall (y Int) (implies (exists (d Int) (= y (* 65 d))) (exists (d Int) (= y (* 5 d)))))");


    test_formula(l_true, 
                 "(exists (z Int) (forall (w Int) (exists (x Int) (y Int) "
                 "  (or (and (< (+ (* 3 x) w) 2) (< 1 (- (+ (* 2 x) z) w))) "
                 "      (and (< z (* 2 y)) (> z y))))))");


    test_formula(l_true, "(exists (x Int) (y Int) (and (> x 0) (>= y 0) (= 1 (- (* 3 x) (* 5 y)))))");


    test_formula(l_true, 
                 "(exists (a Int) (b Int) "
                 "  (and (not (= a 1)) (= a b) (or (= a (* 2 b)) (= (* 2 b) (+ 1 (* 3 a))))))");



    test_formula(l_true, 
                 "(forall (x Int) (iff (and (not (= 0 (mod x 2))) (= 0 (mod (- x 1) 3))) "
                 "                        (or (= 0 (mod (- x 1) 12)) (= 0 (mod (- x 7) 12)))))");






    test_formula(l_false, "(exists (x Int) (and (< (* 3 x) 2) (< 1 (* 2 x))))");


    test_formula(l_true, "(forall (x Int) (y Int) (or (= 0 (mod x 5))                (not (= (* 6 x) (* 5 y)))))");


    test_formula(l_false, "(forall (x Int) (exists (y Int) (= x (* 2 y))))");
    test_formula(l_false, 
                 "(forall (x Int) "
                 "  (implies (not (= 0 (mod x 2))) "
                 "       (or (= 0 (mod (- x 1) 4)) "
                 "           (= 0 (mod (- x 1) 8)) "
                 "           (= 0 (mod (- x 3) 8)) "
                 "           (= 0 (mod (- x 1) 6)) "
                 "           (= 0 (mod (- x 1) 14)) "
                 "           (= 0 (mod (- x 9) 14)) "
                 "           (= 0 (mod (- x 11) 14)) "
                 "           (= 0 (mod (- x 5) 24)) "
                 "           (= 0 (mod (- x 11) 24))))) ");

    test_formula(l_true, 
                 "(forall (x Int) (iff (and (not (= 0 (mod x 2))) (= 0 (mod (- x 1) 3))) "
                 "                        (or (= 0 (mod (- x 1) 12)) (= 0 (mod (- x 7) 12)))))");
    



    test_formula(l_false, 
                 "(forall (d Int) (c Int) (b Int) "
                 "     (and (= c 0) (= d (* b c)) (= d 0)))");




    //return;

    test_formula(l_undef, "(exists (k!12 Int) (k!11 Int) (and (= (ite (= k!11 0) 0 k!11) k!11) (not (= (ite (= k!12 (+ 1)) 1 0) 0))))");
    //return;





    test_formula(l_false, 
                 "(forall (a Int) (b Int) (x Int) (y Int) (z Int) "
                 "  (implies (and (= (+ a 2) b) (= x (+ 1 (- b a))) (= y (- b 2)) (= z 3)) false))");



    test_formula(l_false, 
                 "(exists (a Int) (b Int) "
                 "  (and (> a 1) (> b 1) (= a b) (or (= a (* 2 b)) (= (* 2 b) (+ 1 (* 3 a))))))");



    test_formula(l_true,  "(forall (d Int) (implies true     (exists (x Int) (y Int) (and true     true     (= d (+ (* 3 x) (* 5 y)))))))");

    // This one takes forever without bit-vectors
    test_formula(l_true,  "(forall (d Int) (implies (>= d 8) (exists (x Int) (y Int) (and (>= x 0) (>= y 0) (= d (+ (* 3 x) (* 5 y)))))))");

    test_formula(l_true, "(forall (d Int) (implies (>= d 0) (exists (x Int) (y Int) (and (>= x 0) (>= y 0) (= d (- (* 3 x) (* 5 y)))))))");

    
    test_formula(l_false, "(exists (x Int) (y Int) (z Int) (= 1 (- (* 4 x) (* 6 y))))");

    //return;



    test_formula(l_true, 
                 "(exists (l Int) (forall (x Int) (implies (>= x l) "
                 "       (exists (u Int) (v Int) (and (>= u 0) (>= v 0) (= x (+ (* 3 u) (* 8 v))))))))");

    test_formula(l_true, 
                 "(exists (l Int) (forall (x Int) (implies (>= x l) "
                 "       (exists (u Int) (v Int) (and (>= u 0) (>= v 0) (= x (+ (* 3 u) (* 8 v))))))))");

#if 0

    // too slow.

    test_formula(l_true, 
                 "(exists (l Int) (forall (x Int) (implies (>= x l) "
                 "       (exists (u Int) (v Int) (and (>= u 0) (>= v 0) (= x (+ (* 7 u) (* 8 v))))))))");


#endif

    test_formula(l_true, "(forall (x Int) (exists (y Int) (and (<= (* 2 y) x) (< x (* 2 (+ y 1))))))");


    test_formula(l_false, "(exists (x Int) (y Int) (and (> y 0) (> y (* 2 x)) (< y (+ x 2)) (= 0 (mod y 2))))");

    test_formula(l_false, "(exists (x Int) (and (< (* 3 x) 3) (< 1 (* 2 x))))");


    test_formula(l_true,  "(exists (x Int) (and (< (* 3 x) 4) (< 1 (* 2 x))))");

    test_formula(l_false, "(exists (x Int) (and (< (+ (* 3 x) 1) 10) (> (- (* 7 x) 6) 7) (= 0 (mod x 3))))");


    test_formula(l_false, "(exists (x Int) (y Int) (and (< (- 1 (* 5 y)) x) (< (+ 1 y) (* 13 x)) (< (+ x 2) 0) (> y 0)))");    
    
    test_formula(l_false, "(exists (x Int) (y Int) (and (< (- 1 (* 5 y)) x) (< (+ 1 y) (* 13 x)) (< x -2)))");
    
    test_formula(l_true, "(exists (w Int) (z Int) (y Int) (x Int) (and (< (- 1 (* 5 y)) (+ x (* 2 z))) (< (+ 1 y w (* -4 z)) (* 13 x)) (< x -2) (> z 0)))");

    
    
    test_formula(l_true, 
                 "(forall (w Int) "
                 "  (exists (z Int) (y Int) (x Int) "
                 "    (and (< (- 1 (* 5 y)) (+ x (* 2 z))) "
                 "         (< (- (+ 1 y) (* 4 z)) (* 13 x)) "
                 "         (< x -2) (> z 0) (< x 10))))     ");
    
    
    test_formula(l_false, 
                 "(forall (d Int) (c Int) (b Int) "
                 "     (and (= c 0) (= d (* b c)) (= d 4)))");

    test_formula(l_undef, 
                 "(exists (d Int) (c Int) (b Int) "
                 "     (and (= c 0) (= d (* b c)) (= d 0)))");
    
    test_formula(l_undef, 
                 "(exists (d Int) (c Int) (b Int) "
                 "     (and (= c 0) (= d (* b c)) (= d 4)))");



    // Tests from Harrison's HOL-light version of Cooper.

    test_formula(l_true, "(forall (x Int) (y Int) (not (= (+ 1 (* 2 x)) (* 2 y))))");


    test_formula(l_false, "(exists (x Int) (y Int) (= 1 (- (* 4 x) (* 6 y))))");



    // "(forall (x Int) (implies (< b x) (<= a x)))"
    // "(forall (x Int) (implies (< b x) (< a x)))"


    test_formula(l_false, "(forall (d Int) (implies (>= d 0) (exists (x Int) (y Int) (and (>= x 0) (>= y 0) (= d (+ (* 3 x) (* 5 y)))))))");

    test_formula(l_true,  "(forall (d Int) (implies true     (exists (x Int) (y Int) (and true     true     (= d (+ (* 3 x) (* 5 y)))))))");

    // This one takes forever without bit-vectors
    test_formula(l_true,  "(forall (d Int) (implies (>= d 8) (exists (x Int) (y Int) (and (>= x 0) (>= y 0) (= d (+ (* 3 x) (* 5 y)))))))");

    test_formula(l_true, "(forall (d Int) (implies (>= d 0) (exists (x Int) (y Int) (and (>= x 0) (>= y 0) (= d (- (* 3 x) (* 5 y)))))))");

    test_formula(l_true, "(exists (x Int) (y Int) (and (> x 0) (>= y 0) (= 1 (- (* 3 x) (* 5 y)))))");
    
    test_formula(l_false, "(exists (x Int) (y Int) (z Int) (= 1 (- (* 4 x) (* 6 y))))");

    // "(forall (x Int) (implies (< b (* 3 x)) (a < (* 3 x))))"

    test_formula(l_false, "(forall (x Int) (y Int) (implies (<= x y) (< (+ 1 (* 2 x)) (* 2 y))))");

    
    test_formula(l_true, "(forall (x Int) (y Int) (z Int) (implies (= (+ 1 (* 2 x)) (* 2 y)) (> (+ x y z) 129)))");
    
    // Formula examples from Cooper's paper.                                    


    test_formula(l_true, "(forall (a Int) (exists (b Int) (or (< a (+ (* 4 b) (* 3 a))) (and (not (< a b)) (> a (+ b 1))))))");

    test_formula(l_false, "(exists (y Int) (forall (x Int) (and (> (+ x (* 5 y)) 1) (> (- (* 13 x) y) 1) (< (+ x 2) 0))))");

    // Harrison's formulas:

    test_formula(l_false, "(forall (x Int) (y Int) (implies (and (>= x 0) (>= y 0)) (or (< (- (* 12 x) (* 8 y)) 0) (> (- (* 12 x) (* 8 y)) 2))))");


    //    test_formula(l_true, "(exists (x Int) (y Int) (= 1 (+ (* 5 x) (* 3 y))))");


    test_formula(l_false, "(exists (x Int) (y Int) (= 1 (+ (* 5 x) (* 10 y))))");

    test_formula(l_true, "(exists (x Int) (y Int) (and (>= x 0) (>= y 0) (= 1 (- (* 5 x) (* 6 y)))))");

    test_formula(l_true, "(exists (x Int) (y Int) (z Int) (w Int) (= 1 (+ (* 2 w) (* 3 x) (* 4 y) (* 5 z))))");

    test_formula(l_true, "(exists (x Int) (y Int) (and (>= x 0) (>= y 0) (= 1 (- (* 5 x) (* 3 y)))))");

    test_formula(l_true, "(exists (x Int) (y Int) (and (>= x 0) (>= y 0) (= 1 (- (* 3 x) (* 5 y)))))");

    test_formula(l_false,"(exists (x Int) (y Int) (and (>= x 0) (>= y 0) (= 1 (- (* 6 x) (* 3 y)))))");

    test_formula(l_true, "(forall (x Int) (y Int) (or (= 0 (mod x 5)) (= 0 (mod y 6)) (not (= (* 6 x) (* 5 y)))))");


    test_formula(l_false,"(forall (x Int) (y Int) (or                                (not (= (* 6 x) (* 5 y)))))");


   
    // Positive variant of the Bezout theorem (see the exercise).                *)

    test_formula(l_true, "(forall (z Int) (implies (> z 7) (exists (x Int) (y Int) (and (>= x 0) (>= y 0) (= (+ (* 3 x) (* 5 y)) z)))))");

    test_formula(l_false,"(forall (z Int) (implies (> z 2) (exists (x Int) (y Int) (and (>= x 0) (>= y 0) (= (+ (* 3 x) (* 5 y)) z)))))");

    test_formula(l_true, 
                 "(forall (z Int) (implies (<= z 7) "
                 "    (iff      (exists (x Int) (y Int) (and (>= x 0) (>= y 0) (= z (+ (* 3 x) (* 5 y))))) "
                 "         (not (exists (x Int) (y Int) (and (>= x 0) (>= y 0) (= (- 7 z) (+ (* 3 x) (* 5 y))))))))) ");

    // Basic result about congruences.                                          

    test_formula(l_true, 
                 "(forall (x Int) "
                 "  (iff (and (not (exists (m Int) (= x (* 2 m)))) (exists (m Int) (= x (+ (* 3 m) 1)))) "
                 "       (or  (exists (m Int) (= x (+ (* 12 m) 1))) (exists (m Int) (= x (+ (* 12 m) 7))))))");





    // Inspired by the Collatz conjecture.                                      

    test_formula(l_false, 
                 "(forall (a Int) (b Int) (x Int) (y Int) (z Int) "
                 "  (implies (and (= (+ a 2) b) (= x (+ 1 (- b a))) (= y (- b 2)) (= z 3)) false))");

    test_formula(l_true, 
                 "(exists (a Int) (b Int) "
                 "  (and (not (= a 1)) (= a b) (or (= a (* 2 b)) (= (* 2 b) (+ 1 (* 3 a))))))");


    test_formula(l_false, 
                 "(exists (a Int) (b Int) "
                 "  (and (> a 1) (> b 1) (= a b) (or (= a (* 2 b)) (= (* 2 b) (+ 1 (* 3 a))))))");

    test_formula(l_false, 
                 "(exists (a Int) (b Int) "
                 "  (and (> a 1) (> b 1)  "
                 "    (or (= a (* 2 b)) (= (* 2 b) (+ 1 (* 3 a)))) "
                 "    (or (= b (* 2 a)) (= (* 2 a) (+ 1 (* 3 b))))))");

#if 0
    // Bob Constable's "stamp problem".

    test_formula(l_true, 
                 "(forall (x Int) (implies (>= x 8) "
                 "       (exists (u Int) (v Int) (and (>= u 0) (>= v 0) (= x (+ (* 3 u) (* 5 v)))))))");

    test_formula(l_true, 
                 "(exists (l Int) (forall (x Int) (implies (>= x l) "
                 "       (exists (u Int) (v Int) (and (>= u 0) (>= v 0) (= x (+ (* 3 u) (* 5 v))))))))");

    test_formula(l_true, 
                 "(exists (l Int) (forall (x Int) (implies (>= x l) "
                 "       (exists (u Int) (v Int) (and (>= u 0) (>= v 0) (= x (+ (* 3 u) (* 7 v))))))))");

    test_formula(l_true, 
                 "(exists (l Int) (forall (x Int) (implies (>= x l) "
                 "       (exists (u Int) (v Int) (and (>= u 0) (>= v 0) (= x (+ (* 3 u) (* 8 v))))))))");

    test_formula(l_true, 
                 "(exists (l Int) (forall (x Int) (implies (>= x l) "
                 "       (exists (u Int) (v Int) (and (>= u 0) (>= v 0) (= x (+ (* 7 u) (* 8 v))))))))");
#endif

    // Example from reciprocal mult: (2622 * x)>>16 = x/100 within a range.     


    test_formula(l_true, 
                 "(forall (x Int) (y Int) "
                 "  (iff (exists (d Int) (= (+ x y) (* 2 d))) "
                 "       (iff (exists (d Int) (= x (* 2 d))) (exists (d Int) (= y (* 2 d))))))");

    test_formula(l_true, 
                 "(forall (n Int) "
                 " (implies (and (< 0 n) (< n 2400)) "
                 "     (or (and (<= n 2) (<= 2 (* 2 n))) "
                 "         (and (<= n 3) (<= 3 (* 2 n))) "
                 "         (and (<= n 5) (<= 5 (* 2 n))) "
                 "         (and (<= n 7) (<= 7 (* 2 n))) "
                 "         (and (<= n 13) (<= 13 (* 2 n))) "
                 "         (and (<= n 23) (<= 23 (* 2 n))) "
                 "         (and (<= n 43) (<= 43 (* 2 n))) "
                 "         (and (<= n 83) (<= 83 (* 2 n))) "
                 "         (and (<= n 163) (<= 163 (* 2 n))) "
                 "         (and (<= n 317) (<= 317 (* 2 n))) "
                 "         (and (<= n 631) (<= 631 (* 2 n))) "
                 "         (and (<= n 1259) (<= 1259 (* 2 n))) "
                 "         (and (<= n 2503) (<= 2503 (* 2 n)))))) ");


   

    memory::finalize();
#ifdef _WINDOWS
    _CrtDumpMemoryLeaks();
#endif
    exit(0);
}


