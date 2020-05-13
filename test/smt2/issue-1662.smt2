; Copyright (c) 2018 Microsoft Corporation
; GitHub Issue

(set-logic QF_S)

(declare-fun var () String)
(declare-fun sv1 () String)
(declare-fun sv2 () String)

(assert (= true (= sv1 sv2 ) ))

(assert (= true (str.in.re var (re.++ (re.++ (re.++  (re.++ (re.* re.allchar )
(re.++  (str.to.re "'") (re.++ (re.+  (str.to.re " ") ) (re.++  (re.union
(str.to.re "O")  (str.to.re "o")) (re.++  (re.union  (str.to.re "R")
(str.to.re "r")) (re.++ (re.+  (str.to.re " ") )  (str.to.re "'")))))))
(str.to.re sv1) ) (re.++  (re.++  (str.to.re "'") (re.++ (re.* re.allchar )
(re.++  (str.to.re "=") (re.++ (re.* re.allchar )  (str.to.re "'")))))
(str.to.re sv2) ) )  (re.++  (str.to.re "'") (re.++ (re.*  (str.to.re " ") )
(re.union  (re.++  (str.to.re "\x2d")  (str.to.re "\x2d"))  (str.to.re
"\x23")))) ) ) ))

(check-sat)
