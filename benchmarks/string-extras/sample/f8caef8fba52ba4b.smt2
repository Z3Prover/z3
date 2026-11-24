; origin: https://github.com/plfm-iis/trauc_benchmarks : biopython_laterBio.Phylo._cdao_owlresolve_uriformula6_sat.smt2
(set-logic ALL)
(declare-const s String)
(declare-const cdao_to_obo Bool)
(declare-const xml_style Bool)
(assert cdao_to_obo)
(assert (not (< (str.len s) 0)))
(assert (not (str.prefixof "cdao:" s)))
(assert (not xml_style))
(assert (not (< (str.len s) 0)))
(assert (not (= (+ 0 (str.indexof s "cdao:" 0)) (- 1))))
(check-sat)



