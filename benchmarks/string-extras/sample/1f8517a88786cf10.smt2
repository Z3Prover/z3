; origin: https://github.com/plfm-iis/trauc_benchmarks : biopythonBio.GenBank.__init___FeatureConsumer.tsaformula6_unsat.smt2
(set-logic ALL)
(declare-const self String)
(declare-const content String)
(assert (not (< (str.len content) 0)))
(assert (not (= (+ 0 (str.indexof content "-" 0)) (- 1))))
(assert (not (< (+ 0 (str.indexof content "-" 0)) 0)))
(assert (not (< (+ (+ 0 (str.indexof content "-" 0)) 1) 0)))
(assert (< (str.len content) 0))
(check-sat)


