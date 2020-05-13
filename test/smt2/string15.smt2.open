; noissue
; acknowledgements: Carsten Varming from Amazon

(set-option :smt.string_solver seq)
(declare-const s String)
(assert (str.in.re s (re.++ (str.to.re "ab") re.all (str.to.re "b") re.all (str.to.re "b") re.all (str.to.re "b"))))
(assert (not (str.in.re s (re.++ (str.to.re "a") re.all (str.to.re "b") re.all (str.to.re "b") re.all (str.to.re "b")))))
(check-sat)
(reset)

(set-option :smt.string_solver z3str3)
(declare-const s String)
(assert (str.in.re s (re.++ (str.to.re "ab") re.all (str.to.re "b") re.all (str.to.re "b") re.all (str.to.re "b"))))
(assert (not (str.in.re s (re.++ (str.to.re "a") re.all (str.to.re "b") re.all (str.to.re "b") re.all (str.to.re "b")))))
(check-sat)
