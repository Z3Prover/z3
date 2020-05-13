;; Copyright (c) 2016 Microsoft Corporation 

(set-info :source |Written by D. B. Staple for GitHub issue #623.|)
(set-info :status sat)

(declare-fun n () Int)
(assert (not (< n 1)))
(check-sat-using (par-or qflia smt))
