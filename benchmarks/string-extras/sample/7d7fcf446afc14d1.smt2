; origin: https://github.com/plfm-iis/trauc_benchmarks : biopythonBio.GenBank.ScannerEmblScanner._feed_first_line_newformula5_unsat.smt2
(set-logic ALL)
(declare-const consumer String)
(declare-const line String)
(assert (= (str.substr line 0 (- 5 0)) "ID"))
(assert (not (< (str.len line) 0)))
(assert (not (< (str.len (str.substr line 5 (- (str.len line) 5))) 0)))
(assert (= (+ 0 (str.indexof (str.substr line 5 (- (str.len line) 5)) ";" 0)) (- 1)))
(assert (not (= (str.substr line 5 (- (str.len line) 5)) "")))
(check-sat)


