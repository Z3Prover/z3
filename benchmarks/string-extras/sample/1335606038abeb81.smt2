; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_765.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = [({]?(0x)?[0-9a-fA-F]{8}([-,]?(0x)?[0-9a-fA-F]{4}){2}((-?[0-9a-fA-F]{4}-?[0-9a-fA-F]{12})|(,\{0x[0-9a-fA-F]{2}(,0x[0-9a-fA-F]{2}){7}\}))[)}]?
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "B0xdAC8F09C43890x8F8c-9Aafa97941499aF5"
(define-fun Witness1 () String (str.++ "B" (str.++ "0" (str.++ "x" (str.++ "d" (str.++ "A" (str.++ "C" (str.++ "8" (str.++ "F" (str.++ "0" (str.++ "9" (str.++ "C" (str.++ "4" (str.++ "3" (str.++ "8" (str.++ "9" (str.++ "0" (str.++ "x" (str.++ "8" (str.++ "F" (str.++ "8" (str.++ "c" (str.++ "-" (str.++ "9" (str.++ "A" (str.++ "a" (str.++ "f" (str.++ "a" (str.++ "9" (str.++ "7" (str.++ "9" (str.++ "4" (str.++ "1" (str.++ "4" (str.++ "9" (str.++ "9" (str.++ "a" (str.++ "F" (str.++ "5" "")))))))))))))))))))))))))))))))))))))))
;witness2: "(9e98DA9B-04acC9998f9f-afb882bF96af"
(define-fun Witness2 () String (str.++ "(" (str.++ "9" (str.++ "e" (str.++ "9" (str.++ "8" (str.++ "D" (str.++ "A" (str.++ "9" (str.++ "B" (str.++ "-" (str.++ "0" (str.++ "4" (str.++ "a" (str.++ "c" (str.++ "C" (str.++ "9" (str.++ "9" (str.++ "9" (str.++ "8" (str.++ "f" (str.++ "9" (str.++ "f" (str.++ "-" (str.++ "a" (str.++ "f" (str.++ "b" (str.++ "8" (str.++ "8" (str.++ "2" (str.++ "b" (str.++ "F" (str.++ "9" (str.++ "6" (str.++ "a" (str.++ "f" ""))))))))))))))))))))))))))))))))))))

(assert (= regexA (re.++ (re.opt (re.union (re.range "(" "(") (re.range "{" "{")))(re.++ (re.opt (str.to_re (str.++ "0" (str.++ "x" ""))))(re.++ ((_ re.loop 8 8) (re.union (re.range "0" "9")(re.union (re.range "A" "F") (re.range "a" "f"))))(re.++ ((_ re.loop 2 2) (re.++ (re.opt (re.range "," "-"))(re.++ (re.opt (str.to_re (str.++ "0" (str.++ "x" "")))) ((_ re.loop 4 4) (re.union (re.range "0" "9")(re.union (re.range "A" "F") (re.range "a" "f")))))))(re.++ (re.union (re.++ (re.opt (re.range "-" "-"))(re.++ ((_ re.loop 4 4) (re.union (re.range "0" "9")(re.union (re.range "A" "F") (re.range "a" "f"))))(re.++ (re.opt (re.range "-" "-")) ((_ re.loop 12 12) (re.union (re.range "0" "9")(re.union (re.range "A" "F") (re.range "a" "f"))))))) (re.++ (str.to_re (str.++ "," (str.++ "{" (str.++ "0" (str.++ "x" "")))))(re.++ ((_ re.loop 2 2) (re.union (re.range "0" "9")(re.union (re.range "A" "F") (re.range "a" "f"))))(re.++ ((_ re.loop 7 7) (re.++ (str.to_re (str.++ "," (str.++ "0" (str.++ "x" "")))) ((_ re.loop 2 2) (re.union (re.range "0" "9")(re.union (re.range "A" "F") (re.range "a" "f")))))) (re.range "}" "}"))))) (re.opt (re.union (re.range ")" ")") (re.range "}" "}"))))))))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
