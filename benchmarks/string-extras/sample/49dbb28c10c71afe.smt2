; origin: https://github.com/plfm-iis/trauc_benchmarks : biopythonBio.Align.AlignInfoSummaryInfo._pair_replacementformula192_sat.smt2
(set-logic ALL)
(declare-const self String)
(declare-const seq1 String)
(declare-const seq2 String)
(declare-const weight1 String)
(declare-const weight2 String)
(declare-const dictionary String)
(declare-const letters String)
(assert (< 0 (str.len seq1)))
(assert (< 0 (str.len seq2)))
(assert (not (str.contains letters (str.at seq1 0))))
(assert (< 1 (str.len seq1)))
(assert (< 1 (str.len seq2)))
(assert (str.contains letters (str.at seq1 1)))
(assert (not (str.contains letters (str.at seq2 1))))
(assert (< 2 (str.len seq1)))
(assert (< 2 (str.len seq2)))
(assert (str.contains letters (str.at seq1 2)))
(assert (not (str.contains letters (str.at seq2 2))))
(assert (< 3 (str.len seq1)))
(assert (< 3 (str.len seq2)))
(assert (str.contains letters (str.at seq1 3)))
(assert (not (str.contains letters (str.at seq2 3))))
(assert (< 4 (str.len seq1)))
(assert (< 4 (str.len seq2)))
(assert (str.contains letters (str.at seq1 4)))
(assert (str.contains letters (str.at seq2 4)))
(check-sat)







