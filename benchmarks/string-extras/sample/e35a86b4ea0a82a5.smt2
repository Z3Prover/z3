; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_41.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = \w+([-+.']\w+)*@\w+([-.]\w+)*\.\w+([-.]\w+)*
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "\x18\x1B\u00AA-\u00C8@_\u00B59.\u00B59.i.89\u00F7"
(define-fun Witness1 () String (str.++ "\u{18}" (str.++ "\u{1b}" (str.++ "\u{aa}" (str.++ "-" (str.++ "\u{c8}" (str.++ "@" (str.++ "_" (str.++ "\u{b5}" (str.++ "9" (str.++ "." (str.++ "\u{b5}" (str.++ "9" (str.++ "." (str.++ "i" (str.++ "." (str.++ "8" (str.++ "9" (str.++ "\u{f7}" "")))))))))))))))))))
;witness2: "x\u00BAq.\u00DC\u00D1@9E\u00E18.\u00BA\u00D5.\u00BA\u00BA"
(define-fun Witness2 () String (str.++ "x" (str.++ "\u{ba}" (str.++ "q" (str.++ "." (str.++ "\u{dc}" (str.++ "\u{d1}" (str.++ "@" (str.++ "9" (str.++ "E" (str.++ "\u{e1}" (str.++ "8" (str.++ "." (str.++ "\u{ba}" (str.++ "\u{d5}" (str.++ "." (str.++ "\u{ba}" (str.++ "\u{ba}" ""))))))))))))))))))

(assert (= regexA (re.++ (re.+ (re.union (re.range "0" "9")(re.union (re.range "A" "Z")(re.union (re.range "_" "_")(re.union (re.range "a" "z")(re.union (re.range "\u{aa}" "\u{aa}")(re.union (re.range "\u{b5}" "\u{b5}")(re.union (re.range "\u{ba}" "\u{ba}")(re.union (re.range "\u{c0}" "\u{d6}")(re.union (re.range "\u{d8}" "\u{f6}") (re.range "\u{f8}" "\u{ff}")))))))))))(re.++ (re.* (re.++ (re.union (re.range "'" "'")(re.union (re.range "+" "+") (re.range "-" "."))) (re.+ (re.union (re.range "0" "9")(re.union (re.range "A" "Z")(re.union (re.range "_" "_")(re.union (re.range "a" "z")(re.union (re.range "\u{aa}" "\u{aa}")(re.union (re.range "\u{b5}" "\u{b5}")(re.union (re.range "\u{ba}" "\u{ba}")(re.union (re.range "\u{c0}" "\u{d6}")(re.union (re.range "\u{d8}" "\u{f6}") (re.range "\u{f8}" "\u{ff}")))))))))))))(re.++ (re.range "@" "@")(re.++ (re.+ (re.union (re.range "0" "9")(re.union (re.range "A" "Z")(re.union (re.range "_" "_")(re.union (re.range "a" "z")(re.union (re.range "\u{aa}" "\u{aa}")(re.union (re.range "\u{b5}" "\u{b5}")(re.union (re.range "\u{ba}" "\u{ba}")(re.union (re.range "\u{c0}" "\u{d6}")(re.union (re.range "\u{d8}" "\u{f6}") (re.range "\u{f8}" "\u{ff}")))))))))))(re.++ (re.* (re.++ (re.range "-" ".") (re.+ (re.union (re.range "0" "9")(re.union (re.range "A" "Z")(re.union (re.range "_" "_")(re.union (re.range "a" "z")(re.union (re.range "\u{aa}" "\u{aa}")(re.union (re.range "\u{b5}" "\u{b5}")(re.union (re.range "\u{ba}" "\u{ba}")(re.union (re.range "\u{c0}" "\u{d6}")(re.union (re.range "\u{d8}" "\u{f6}") (re.range "\u{f8}" "\u{ff}")))))))))))))(re.++ (re.range "." ".")(re.++ (re.+ (re.union (re.range "0" "9")(re.union (re.range "A" "Z")(re.union (re.range "_" "_")(re.union (re.range "a" "z")(re.union (re.range "\u{aa}" "\u{aa}")(re.union (re.range "\u{b5}" "\u{b5}")(re.union (re.range "\u{ba}" "\u{ba}")(re.union (re.range "\u{c0}" "\u{d6}")(re.union (re.range "\u{d8}" "\u{f6}") (re.range "\u{f8}" "\u{ff}"))))))))))) (re.* (re.++ (re.range "-" ".") (re.+ (re.union (re.range "0" "9")(re.union (re.range "A" "Z")(re.union (re.range "_" "_")(re.union (re.range "a" "z")(re.union (re.range "\u{aa}" "\u{aa}")(re.union (re.range "\u{b5}" "\u{b5}")(re.union (re.range "\u{ba}" "\u{ba}")(re.union (re.range "\u{c0}" "\u{d6}")(re.union (re.range "\u{d8}" "\u{f6}") (re.range "\u{f8}" "\u{ff}"))))))))))))))))))))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
