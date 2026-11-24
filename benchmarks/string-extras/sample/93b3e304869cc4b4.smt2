; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_741.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = (4\d{12})|(((4|3)\d{3})|(5[1-5]\d{2})|(6011))(-?|\040?)(\d{4}(-?|\040?)){3}|((3[4,7]\d{2})((-?|\040?)\d{6}(-?|\040?)\d{5}))|(3[4,7]\d{2})((-?|\040?)\d{4}(-?|\040?)\d{4}(-?|\040?)\d{3})|(3[4,7]\d{1})(-?|\040?)(\d{4}(-?|\040?)){3}|(30[0-5]\d{1}|(36|38)\d(2))((-?|\040?)\d{4}(-?|\040?)\d{4}(-?|\040?)\d{2})|((2131|1800)|(2014|2149))((-?|\040?)\d{4}(-?|\040?)\d{4}(-?|\040?)\d{3})
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "3,4 9780-8748 8992-"
(define-fun Witness1 () String (str.++ "3" (str.++ "," (str.++ "4" (str.++ " " (str.++ "9" (str.++ "7" (str.++ "8" (str.++ "0" (str.++ "-" (str.++ "8" (str.++ "7" (str.++ "4" (str.++ "8" (str.++ " " (str.++ "8" (str.++ "9" (str.++ "9" (str.++ "2" (str.++ "-" ""))))))))))))))))))))
;witness2: "3790 09088890-7986"
(define-fun Witness2 () String (str.++ "3" (str.++ "7" (str.++ "9" (str.++ "0" (str.++ " " (str.++ "0" (str.++ "9" (str.++ "0" (str.++ "8" (str.++ "8" (str.++ "8" (str.++ "9" (str.++ "0" (str.++ "-" (str.++ "7" (str.++ "9" (str.++ "8" (str.++ "6" "")))))))))))))))))))

(assert (= regexA (re.union (re.++ (re.range "4" "4") ((_ re.loop 12 12) (re.range "0" "9")))(re.union (re.++ (re.union (re.++ (re.range "3" "4") ((_ re.loop 3 3) (re.range "0" "9")))(re.union (re.++ (re.range "5" "5")(re.++ (re.range "1" "5") ((_ re.loop 2 2) (re.range "0" "9")))) (str.to_re (str.++ "6" (str.++ "0" (str.++ "1" (str.++ "1" "")))))))(re.++ (re.union (re.opt (re.range "-" "-")) (re.opt (re.range " " " "))) ((_ re.loop 3 3) (re.++ ((_ re.loop 4 4) (re.range "0" "9")) (re.union (re.opt (re.range "-" "-")) (re.opt (re.range " " " ")))))))(re.union (re.++ (re.++ (re.range "3" "3")(re.++ (re.union (re.range "," ",")(re.union (re.range "4" "4") (re.range "7" "7"))) ((_ re.loop 2 2) (re.range "0" "9")))) (re.++ (re.union (re.opt (re.range "-" "-")) (re.opt (re.range " " " ")))(re.++ ((_ re.loop 6 6) (re.range "0" "9"))(re.++ (re.union (re.opt (re.range "-" "-")) (re.opt (re.range " " " "))) ((_ re.loop 5 5) (re.range "0" "9"))))))(re.union (re.++ (re.++ (re.range "3" "3")(re.++ (re.union (re.range "," ",")(re.union (re.range "4" "4") (re.range "7" "7"))) ((_ re.loop 2 2) (re.range "0" "9")))) (re.++ (re.union (re.opt (re.range "-" "-")) (re.opt (re.range " " " ")))(re.++ ((_ re.loop 4 4) (re.range "0" "9"))(re.++ (re.union (re.opt (re.range "-" "-")) (re.opt (re.range " " " ")))(re.++ ((_ re.loop 4 4) (re.range "0" "9"))(re.++ (re.union (re.opt (re.range "-" "-")) (re.opt (re.range " " " "))) ((_ re.loop 3 3) (re.range "0" "9"))))))))(re.union (re.++ (re.++ (re.range "3" "3")(re.++ (re.union (re.range "," ",")(re.union (re.range "4" "4") (re.range "7" "7"))) (re.range "0" "9")))(re.++ (re.union (re.opt (re.range "-" "-")) (re.opt (re.range " " " "))) ((_ re.loop 3 3) (re.++ ((_ re.loop 4 4) (re.range "0" "9")) (re.union (re.opt (re.range "-" "-")) (re.opt (re.range " " " ")))))))(re.union (re.++ (re.union (re.++ (str.to_re (str.++ "3" (str.++ "0" "")))(re.++ (re.range "0" "5") (re.range "0" "9"))) (re.++ (re.union (str.to_re (str.++ "3" (str.++ "6" ""))) (str.to_re (str.++ "3" (str.++ "8" ""))))(re.++ (re.range "0" "9") (re.range "2" "2")))) (re.++ (re.union (re.opt (re.range "-" "-")) (re.opt (re.range " " " ")))(re.++ ((_ re.loop 4 4) (re.range "0" "9"))(re.++ (re.union (re.opt (re.range "-" "-")) (re.opt (re.range " " " ")))(re.++ ((_ re.loop 4 4) (re.range "0" "9"))(re.++ (re.union (re.opt (re.range "-" "-")) (re.opt (re.range " " " "))) ((_ re.loop 2 2) (re.range "0" "9")))))))) (re.++ (re.union (re.union (str.to_re (str.++ "2" (str.++ "1" (str.++ "3" (str.++ "1" ""))))) (str.to_re (str.++ "1" (str.++ "8" (str.++ "0" (str.++ "0" "")))))) (re.union (str.to_re (str.++ "2" (str.++ "0" (str.++ "1" (str.++ "4" ""))))) (str.to_re (str.++ "2" (str.++ "1" (str.++ "4" (str.++ "9" ""))))))) (re.++ (re.union (re.opt (re.range "-" "-")) (re.opt (re.range " " " ")))(re.++ ((_ re.loop 4 4) (re.range "0" "9"))(re.++ (re.union (re.opt (re.range "-" "-")) (re.opt (re.range " " " ")))(re.++ ((_ re.loop 4 4) (re.range "0" "9"))(re.++ (re.union (re.opt (re.range "-" "-")) (re.opt (re.range " " " "))) ((_ re.loop 3 3) (re.range "0" "9"))))))))))))))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
