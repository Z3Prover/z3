(declare-fun a () String)
(declare-fun b () String)

;(assert (= a "b"))
;(assert (= b ""))

(assert (str.in.re a (re.+ (re.union (str.to.re "z") (str.to.re "b")))))
(assert (str.in.re a (re.opt (re.range "a" "u"))))
(assert (str.in.re (str.++ "b" b) (re.opt (re.range "a" "u"))))
(assert (not (str.in.re (str.++ "b" a) (re.opt (re.+ (re.+ (str.to.re "a")))))))
(check-sat)
(get-model)