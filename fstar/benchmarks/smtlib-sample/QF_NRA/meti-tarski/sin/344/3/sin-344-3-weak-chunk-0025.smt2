(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The meti-tarski benchmarks are proof obligations extracted from the
Meti-Tarski project, see:

  B. Akbarpour and L. C. Paulson. MetiTarski: An automatic theorem prover
  for real-valued special functions. Journal of Automated Reasoning,
  44(3):175-205, 2010.

Submitted by Dejan Jovanovic for SMT-LIB.


|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (let ((?v_0 (* skoX (/ 1 2))) (?v_1 (* skoY (/ 1 2))) (?v_2 (* skoX (/ (- 1) 2)))) (and (not (<= (* skoZ (+ (+ (+ (- 2) (* skoX ?v_0)) (* skoY (+ skoX ?v_1))) (* skoZ (+ (+ ?v_0 ?v_1) (* skoZ (/ 1 3)))))) (+ (+ (/ 1 10) (* skoX (+ 2 (* skoX (* skoX (/ (- 1) 3)))))) (* skoY (+ (+ 2 (* skoX ?v_2)) (* skoY (+ ?v_2 (* skoY (/ (- 1) 3))))))))) (and (not (<= (/ 11 10) skoX)) (and (not (<= (/ 11 10) skoY)) (and (not (<= (/ 11 10) skoZ)) (and (not (<= skoX (/ 1 10))) (and (not (<= skoY (/ 1 10))) (not (<= skoZ (/ 1 10)))))))))))
(check-sat)
(exit)
