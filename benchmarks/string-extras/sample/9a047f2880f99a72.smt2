; origin: https://github.com/plfm-iis/trauc_benchmarks : biopythonBio.Nexus.NexusNexus._formatformula19_sat.smt2
(set-logic ALL)
(declare-const options String)
(assert (str.contains options "respectcase"))
(assert (not (str.contains options "symbols")))
(assert (not (str.contains options "datatype")))
(assert (not (str.contains options "missing")))
(assert (not (str.contains options "gap")))
(assert (not (str.contains options "equate")))
(assert (not (str.contains options "matchchar")))
(assert (str.contains options "labels"))
(check-sat)

