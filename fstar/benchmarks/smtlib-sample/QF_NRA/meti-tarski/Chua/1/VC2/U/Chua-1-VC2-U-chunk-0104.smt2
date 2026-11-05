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
(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (not (<= (* skoX (+ (/ 1728 3125) (* skoX (+ (/ (- 648) 9765625) (* skoX (+ (/ 162 30517578125) (* skoX (+ (/ (- 1701) 6103515625000000) (* skoX (+ (/ 729 76293945312500000000) (* skoX (/ (- 729) 3814697265625000000000000)))))))))))) 2304)) (not (<= skoS (* skoC (/ 3 13))))))
(check-sat)
(exit)
