(set-info :smt-lib-version 2.6)
(set-logic QF_LRA)
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
(declare-fun pi () Real)
(assert (let ((?v_0 (* skoX 10))) (let ((?v_1 (<= ?v_0 skoY)) (?v_3 (<= skoY 0)) (?v_2 (<= skoY ?v_0))) (and (<= 0 skoY) (and ?v_1 (and ?v_3 (and ?v_2 (and (or (not ?v_1) (or (not ?v_2) ?v_3)) (and (not (<= skoY skoX)) (and (<= (/ 1 20) skoX) (and (<= skoY (* pi (/ 1 2))) (and (not (<= (/ 31415927 10000000) pi)) (not (<= pi (/ 15707963 5000000)))))))))))))))
(check-sat)
(exit)
