;; Copyright (c) 2016 Microsoft Corporation

(set-info :source |Written by D. B. Staple for GitHub issue #680.|)
(set-info :status unsat)

(declare-fun theta () Real)
(assert (< (sin theta) -1.0))
(check-sat-using qfnra-nlsat)
(reset)

(declare-fun theta () Real)
(assert (> (sin theta) 1.0))
(check-sat-using qfnra-nlsat)
(reset)

(declare-fun theta () Real)
(assert (< (cos theta) -1.0))
(check-sat-using qfnra-nlsat)
(reset)

(declare-fun theta () Real)
(assert (> (sin theta) 1.0))
(check-sat-using qfnra-nlsat)
