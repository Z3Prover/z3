; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_1075.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = ES\d{2}[ ]\d{4}[ ]\d{4}[ ]\d{4}[ ]\d{4}[ ]\d{4}|ES\d{22}
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "\u0094ES59 4409 9996 9939 8684 9898"
(define-fun Witness1 () String (str.++ "\u{94}" (str.++ "E" (str.++ "S" (str.++ "5" (str.++ "9" (str.++ " " (str.++ "4" (str.++ "4" (str.++ "0" (str.++ "9" (str.++ " " (str.++ "9" (str.++ "9" (str.++ "9" (str.++ "6" (str.++ " " (str.++ "9" (str.++ "9" (str.++ "3" (str.++ "9" (str.++ " " (str.++ "8" (str.++ "6" (str.++ "8" (str.++ "4" (str.++ " " (str.++ "9" (str.++ "8" (str.++ "9" (str.++ "8" "")))))))))))))))))))))))))))))))
;witness2: "ES69 5999 5854 8838 8872 7119"
(define-fun Witness2 () String (str.++ "E" (str.++ "S" (str.++ "6" (str.++ "9" (str.++ " " (str.++ "5" (str.++ "9" (str.++ "9" (str.++ "9" (str.++ " " (str.++ "5" (str.++ "8" (str.++ "5" (str.++ "4" (str.++ " " (str.++ "8" (str.++ "8" (str.++ "3" (str.++ "8" (str.++ " " (str.++ "8" (str.++ "8" (str.++ "7" (str.++ "2" (str.++ " " (str.++ "7" (str.++ "1" (str.++ "1" (str.++ "9" ""))))))))))))))))))))))))))))))

(assert (= regexA (re.union (re.++ (str.to_re (str.++ "E" (str.++ "S" "")))(re.++ ((_ re.loop 2 2) (re.range "0" "9"))(re.++ (re.range " " " ")(re.++ ((_ re.loop 4 4) (re.range "0" "9"))(re.++ (re.range " " " ")(re.++ ((_ re.loop 4 4) (re.range "0" "9"))(re.++ (re.range " " " ")(re.++ ((_ re.loop 4 4) (re.range "0" "9"))(re.++ (re.range " " " ")(re.++ ((_ re.loop 4 4) (re.range "0" "9"))(re.++ (re.range " " " ") ((_ re.loop 4 4) (re.range "0" "9"))))))))))))) (re.++ (str.to_re (str.++ "E" (str.++ "S" ""))) ((_ re.loop 22 22) (re.range "0" "9"))))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
