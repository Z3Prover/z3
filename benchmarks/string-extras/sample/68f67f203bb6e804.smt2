; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_1098.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = ^[F][O][\s]?[0-9]{3}$
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "FO 805"
(define-fun Witness1 () String (str.++ "F" (str.++ "O" (str.++ " " (str.++ "8" (str.++ "0" (str.++ "5" "")))))))
;witness2: "FO\u0085188"
(define-fun Witness2 () String (str.++ "F" (str.++ "O" (str.++ "\u{85}" (str.++ "1" (str.++ "8" (str.++ "8" "")))))))

(assert (= regexA (re.++ (str.to_re "")(re.++ (str.to_re (str.++ "F" (str.++ "O" "")))(re.++ (re.opt (re.union (re.range "\u{09}" "\u{0d}")(re.union (re.range " " " ")(re.union (re.range "\u{85}" "\u{85}") (re.range "\u{a0}" "\u{a0}")))))(re.++ ((_ re.loop 3 3) (re.range "0" "9")) (str.to_re "")))))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
