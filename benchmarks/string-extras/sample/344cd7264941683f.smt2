; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_117.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = [A-Za-z0-9!#$%&'*+\-/=?^_`{|}~]+(?:\.[A-Za-z0-9!#$%&'*+\-/=?^_`{|}~]+)*@[A-Za-z0-9]+(?:-[A-Za-z0-9]+)*(?:\.[A-Za-z0-9]+(?:-[A-Za-z0-9]+)*)*
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "D\u00EAD6.vY#@H0352.N39aIk-0"
(define-fun Witness1 () String (str.++ "D" (str.++ "\u{ea}" (str.++ "D" (str.++ "6" (str.++ "." (str.++ "v" (str.++ "Y" (str.++ "#" (str.++ "@" (str.++ "H" (str.++ "0" (str.++ "3" (str.++ "5" (str.++ "2" (str.++ "." (str.++ "N" (str.++ "3" (str.++ "9" (str.++ "a" (str.++ "I" (str.++ "k" (str.++ "-" (str.++ "0" ""))))))))))))))))))))))))
;witness2: "1.^@99g"
(define-fun Witness2 () String (str.++ "1" (str.++ "." (str.++ "^" (str.++ "@" (str.++ "9" (str.++ "9" (str.++ "g" ""))))))))

(assert (= regexA (re.++ (re.+ (re.union (re.range "!" "!")(re.union (re.range "#" "'")(re.union (re.range "*" "+")(re.union (re.range "-" "-")(re.union (re.range "/" "9")(re.union (re.range "=" "=")(re.union (re.range "?" "?")(re.union (re.range "A" "Z") (re.range "^" "~"))))))))))(re.++ (re.* (re.++ (re.range "." ".") (re.+ (re.union (re.range "!" "!")(re.union (re.range "#" "'")(re.union (re.range "*" "+")(re.union (re.range "-" "-")(re.union (re.range "/" "9")(re.union (re.range "=" "=")(re.union (re.range "?" "?")(re.union (re.range "A" "Z") (re.range "^" "~"))))))))))))(re.++ (re.range "@" "@")(re.++ (re.+ (re.union (re.range "0" "9")(re.union (re.range "A" "Z") (re.range "a" "z"))))(re.++ (re.* (re.++ (re.range "-" "-") (re.+ (re.union (re.range "0" "9")(re.union (re.range "A" "Z") (re.range "a" "z")))))) (re.* (re.++ (re.range "." ".")(re.++ (re.+ (re.union (re.range "0" "9")(re.union (re.range "A" "Z") (re.range "a" "z")))) (re.* (re.++ (re.range "-" "-") (re.+ (re.union (re.range "0" "9")(re.union (re.range "A" "Z") (re.range "a" "z"))))))))))))))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
