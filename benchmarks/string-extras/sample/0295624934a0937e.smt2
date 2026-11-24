; origin: https://github.com/plfm-iis/trauc_benchmarks : biopythonBio.Nexus.NexusNexus._dimensionsformula2_sat.smt2
(set-logic ALL)
(declare-const options String)
(assert (not (str.contains options "ntax")))
(assert (str.contains options "nchar"))
(check-sat)

