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
(assert (let ((?v_0 (* skoX (* skoX 12))) (?v_1 (* skoX 3))) (let ((?v_6 (* skoX ?v_1)) (?v_3 (* skoX 6)) (?v_4 (* skoX 2)) (?v_5 (* skoX (* skoX (- 3)))) (?v_2 (* skoX (- 6)))) (and (not (<= 0 skoY)) (and (not (<= (* skoZ (+ (+ 9 (* skoY (+ (* skoX (- 24)) (* skoY (+ (+ (- 3) (* skoX (* skoX 15))) (* skoY (* skoY ?v_6))))))) (* skoZ (* skoY (+ (- 3) (* skoY (+ ?v_3 (* skoY ?v_5)))))))) (+ (* skoX (- 9)) (* skoY (+ ?v_0 (* skoY (+ ?v_2 (* skoY (+ ?v_0 (* skoY ?v_1)))))))))) (and (not (<= (* skoZ (+ (+ ?v_2 (* skoY (+ (+ (- 6) (* skoX ?v_3)) (* skoY (+ (* skoX 4) (* skoY (+ (+ (- 2) (* skoX ?v_4)) (* skoY ?v_4)))))))) (* skoZ (+ (- 3) (* skoY (+ ?v_3 (* skoY (+ (+ (- 1) ?v_5) (* skoY (+ ?v_4 (* skoY (* skoX (* skoX (- 1)))))))))))))) (+ (+ 9 ?v_6) (* skoY (+ (* skoX (- 12)) (* skoY (+ (+ 6 (* skoX (* skoX 10))) (* skoY (+ (* skoX (- 4)) (* skoY (+ 1 ?v_6))))))))))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= 1 skoY)) (not (<= skoY skoX)))))))))))
(check-sat)
(exit)
