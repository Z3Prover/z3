; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_1340.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = ^((ht|f)tp(s?))\://([0-9a-zA-Z\-]+\.)+[a-zA-Z]{2,6}(\:[0-9]+)?(/\S*)?$
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "https://85-0.Pg"
(define-fun Witness1 () String (str.++ "h" (str.++ "t" (str.++ "t" (str.++ "p" (str.++ "s" (str.++ ":" (str.++ "/" (str.++ "/" (str.++ "8" (str.++ "5" (str.++ "-" (str.++ "0" (str.++ "." (str.++ "P" (str.++ "g" ""))))))))))))))))
;witness2: "https://U.zozUa:41"
(define-fun Witness2 () String (str.++ "h" (str.++ "t" (str.++ "t" (str.++ "p" (str.++ "s" (str.++ ":" (str.++ "/" (str.++ "/" (str.++ "U" (str.++ "." (str.++ "z" (str.++ "o" (str.++ "z" (str.++ "U" (str.++ "a" (str.++ ":" (str.++ "4" (str.++ "1" "")))))))))))))))))))

(assert (= regexA (re.++ (str.to_re "")(re.++ (re.++ (re.union (str.to_re (str.++ "h" (str.++ "t" ""))) (re.range "f" "f"))(re.++ (str.to_re (str.++ "t" (str.++ "p" ""))) (re.opt (re.range "s" "s"))))(re.++ (str.to_re (str.++ ":" (str.++ "/" (str.++ "/" ""))))(re.++ (re.+ (re.++ (re.+ (re.union (re.range "-" "-")(re.union (re.range "0" "9")(re.union (re.range "A" "Z") (re.range "a" "z"))))) (re.range "." ".")))(re.++ ((_ re.loop 2 6) (re.union (re.range "A" "Z") (re.range "a" "z")))(re.++ (re.opt (re.++ (re.range ":" ":") (re.+ (re.range "0" "9"))))(re.++ (re.opt (re.++ (re.range "/" "/") (re.* (re.union (re.range "\u{00}" "\u{08}")(re.union (re.range "\u{0e}" "\u{1f}")(re.union (re.range "!" "\u{84}")(re.union (re.range "\u{86}" "\u{9f}") (re.range "\u{a1}" "\u{ff}")))))))) (str.to_re ""))))))))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
