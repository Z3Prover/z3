; origin: https://github.com/Z3Prover/z3test/tree/master/regressions : smt2/5721.smt2.disabled
(declare-const s String)
(assert (let ((a!1 (re.++ (re.range "0" "9")
(re.* (re.++ (str.to_re "b") (re.range "0" "9")))))
(a!2 (re.++ (re.* (re.++ (re.range "0" "9") (str.to_re "b")))
(re.range "0" "9"))))
(str.in.re s (re.diff (re.++ a!1 a!1) (re.++ a!2 a!2)))))
(check-sat)

(reset)

(declare-fun a () String)
(assert (str.in_re a (re.union
(re.inter
(re.++ (re.++ (re.range "a" "z") (re.* (re.++ (re.range "A" "Z") (re.range "a" "z")))) (re.++ (re.range "a" "z") (re.* (re.++ (re.range "A" "Z") (re.range "a" "z")))))
(re.comp
(re.++ (re.++ (re.* (re.++ (re.range "a" "z") (re.range "A" "Z"))) (re.range "a" "z")) (re.++ (re.* (re.++ (re.range "a" "z") (re.range "A" "Z"))) (re.range "a" "z")))
)
)
(re.inter
(re.++ (re.++ (re.* (re.++ (re.range "a" "z") (re.range "A" "Z"))) (re.range "a" "z")) (re.++ (re.* (re.++ (re.range "a" "z") (re.range "A" "Z"))) (re.range "a" "z")))
(re.comp
(re.++ (re.++ (re.range "a" "z") (re.* (re.++ (re.range "A" "Z") (re.range "a" "z")))) (re.++ (re.range "a" "z") (re.* (re.++ (re.range "A" "Z") (re.range "a" "z")))))
)
)
)))
(check-sat)
(reset)

(declare-const s String)
(assert (str.in_re s (re.+ (re.inter (re.++ ((_ re.loop 0 3) (re.+ (str.to_re "a"))) (str.to_re "c")) (re.* (re.range "a" "b"))))))
(check-sat)
(reset)

(declare-const s String)
(assert (str.in_re s
(re.inter (re.++ (re.++ (re.++ re.all (str.to_re "a")) ((_ re.loop 3 3) re.allchar)) (str.to_re "b")) (re.++ (re.* (str.to_re "a")) (str.to_re "c")))
))
(check-sat)
(reset)