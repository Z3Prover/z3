;; Copyright (c) 2016 Microsoft Corporation

(set-info :source |Written by D. B. Staple for GitHub issue #680.|)
(set-info :status sat)

(declare-fun theta () Real)
(assert (= (sin theta) (cos theta)))
(check-sat-using qfnra-nlsat)
(get-model)
