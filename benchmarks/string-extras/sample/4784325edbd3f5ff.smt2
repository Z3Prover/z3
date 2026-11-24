; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_967.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = test
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "test"
(define-fun Witness1 () String (str.++ "t" (str.++ "e" (str.++ "s" (str.++ "t" "")))))
;witness2: "test\u008E\u0094\u00AC\u00DE\u00AA\u00D2"
(define-fun Witness2 () String (str.++ "t" (str.++ "e" (str.++ "s" (str.++ "t" (str.++ "\u{8e}" (str.++ "\u{94}" (str.++ "\u{ac}" (str.++ "\u{de}" (str.++ "\u{aa}" (str.++ "\u{d2}" "")))))))))))

(assert (= regexA (str.to_re (str.++ "t" (str.++ "e" (str.++ "s" (str.++ "t" "")))))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
