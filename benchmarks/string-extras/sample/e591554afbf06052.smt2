; origin: https://github.com/cdstanford/regex-smt-benchmarks : regexlib_membership/membership_1798.smt2
;---
; using 8-bit bit-vectors as characters
; check membership of .Net regex
; regexA = ^(http|https|ftp)\://[a-zA-Z0-9\-\.]+\.[a-zA-Z]{2,3}(:[a-zA-Z0-9]*)?/?([a-zA-Z0-9\-\._\?\,\'/\\\+&amp;%\$#\=~])*[^\.\,\)\(\s]$
;---
;(set-info :status sat)
;(set-option :print-success true)
(set-logic QF_S)

(declare-const regexA RegLan)
(declare-const x String)

;witness1: "https://8.xy/\u00EF"
(define-fun Witness1 () String (str.++ "h" (str.++ "t" (str.++ "t" (str.++ "p" (str.++ "s" (str.++ ":" (str.++ "/" (str.++ "/" (str.++ "8" (str.++ "." (str.++ "x" (str.++ "y" (str.++ "/" (str.++ "\u{ef}" "")))))))))))))))
;witness2: "https://-.xy:8/L"
(define-fun Witness2 () String (str.++ "h" (str.++ "t" (str.++ "t" (str.++ "p" (str.++ "s" (str.++ ":" (str.++ "/" (str.++ "/" (str.++ "-" (str.++ "." (str.++ "x" (str.++ "y" (str.++ ":" (str.++ "8" (str.++ "/" (str.++ "L" "")))))))))))))))))

(assert (= regexA (re.++ (str.to_re "")(re.++ (re.union (str.to_re (str.++ "h" (str.++ "t" (str.++ "t" (str.++ "p" "")))))(re.union (str.to_re (str.++ "h" (str.++ "t" (str.++ "t" (str.++ "p" (str.++ "s" "")))))) (str.to_re (str.++ "f" (str.++ "t" (str.++ "p" ""))))))(re.++ (str.to_re (str.++ ":" (str.++ "/" (str.++ "/" ""))))(re.++ (re.+ (re.union (re.range "-" ".")(re.union (re.range "0" "9")(re.union (re.range "A" "Z") (re.range "a" "z")))))(re.++ (re.range "." ".")(re.++ ((_ re.loop 2 3) (re.union (re.range "A" "Z") (re.range "a" "z")))(re.++ (re.opt (re.++ (re.range ":" ":") (re.* (re.union (re.range "0" "9")(re.union (re.range "A" "Z") (re.range "a" "z"))))))(re.++ (re.opt (re.range "/" "/"))(re.++ (re.* (re.union (re.range "#" "'")(re.union (re.range "+" "9")(re.union (re.range ";" ";")(re.union (re.range "=" "=")(re.union (re.range "?" "?")(re.union (re.range "A" "Z")(re.union (re.range "\u{5c}" "\u{5c}")(re.union (re.range "_" "_")(re.union (re.range "a" "z") (re.range "~" "~")))))))))))(re.++ (re.union (re.range "\u{00}" "\u{08}")(re.union (re.range "\u{0e}" "\u{1f}")(re.union (re.range "!" "'")(re.union (re.range "*" "+")(re.union (re.range "-" "-")(re.union (re.range "/" "\u{84}")(re.union (re.range "\u{86}" "\u{9f}") (re.range "\u{a1}" "\u{ff}")))))))) (str.to_re "")))))))))))))

;check that the regex contains some x
(assert (str.in_re x regexA))
;check also the concrete witnesses
(assert (str.in_re Witness1 regexA))
(assert (str.in_re Witness2 regexA))
(check-sat)
