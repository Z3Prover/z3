;; Copyright (c) 2017 Microsoft Corporation
(declare-const a String)
(declare-const b String)
(declare-const c String)
(declare-const d String)
(declare-const i Int)
(declare-const j Int)

(set-option :model_validate true)

; extract/substr

(simplify (= "b" (str.substr "abc" 1 1)))

(push)
(set-info :status unsat)
(assert (>= (str.len a) 3))
(assert (= (str.len b) 2))
(assert (= b (str.substr a 1 1)))
(check-sat)
(pop)



(push)
(set-info :status sat)
(assert (= (str.len a) 3))
(assert (= (str.len b) 1))
(assert (= b (str.substr a 1 1)))
(check-sat)
(pop)


(push)
(set-info :status sat)
(assert (= (str.len a) 3))
(assert (= (str.len b) 1))
(assert (= b (str.substr a 2 1)))
(check-sat)
(pop)

(push)
(set-info :status sat)
(assert (= (str.len a) 3))
(assert (= (str.len b) 1))
(assert (= b (str.substr a 0 1)))
(check-sat)
(pop)

(push)
(set-info :status unsat)
(assert (= (str.len a) 3))
(assert (= (str.len b) 1))
(assert (= b (str.substr a 3 1)))
(check-sat)
(pop)

; at

(simplify (= "a" (str.at "abc" 0)))
(simplify (= "b" (str.at "abc" 1)))
(simplify (= "c" (str.at "abc" 2)))

(set-option :model_validate false)
(push)
(set-info :status sat)
(assert (= (seq.len a) 2))
(assert (= b (seq.at a 0)))
(assert (= b (seq.at a 1)))
(check-sat)
(pop)

(push)
(set-info :status sat)
(assert (= b (str.at a i)))
(check-sat)
(pop)


(push)
(set-info :status unsat)
(assert (< i 0))
(assert (= "b" (str.at a i)))
(check-sat)
(pop)

(push)
(set-info :status unsat)
(assert (>= i (str.len a)))
(assert (= "b" (str.at a i)))
(check-sat)
(pop)

(set-option :model_validate true)
(push)
(set-info :status sat)
(assert (<= 0 i))
(assert (< i (str.len a)))
(assert (= "b" (str.at a i)))
(check-sat)
(pop)

(push)
(set-info :status unsat)
(assert (<= 0 i))
(assert (< i (str.len a)))
(assert (= "ab" (str.at a i)))
(check-sat)
(pop)

; contains
(push)
(set-info :status unsat)
(assert (str.contains a b))
(assert (str.contains b c))
(assert (not (str.contains a c)))
(check-sat)
(pop)

(echo "removed")
(push)
(set-info :status sat)
(assert (str.contains a b))
(assert (str.contains a c))
(assert (not (str.contains b c)))
;(check-sat)
(pop)

(push)
(set-info :status unsat)
(assert (str.contains a b))
(assert (str.contains b c))
(assert (str.contains c a))
(assert (not (= a c)))
(check-sat)
(pop)


(echo "removed")
(push)
(set-info :status sat)
(assert (not (str.contains a b)))
(assert (not (str.contains b c)))
(assert (str.contains a c))
;(check-sat)
(pop)



(echo "removed")
(push)
(set-info :status sat)
(assert (not (str.contains a "a")))
(assert (not (str.contains a "b")))
(assert (str.contains a "c"))
;(check-sat)
(pop)


(echo "removed")
(push)
(set-info :status sat)
(assert (not (str.contains a "a")))
(assert (not (str.contains a "b")))
(assert (str.contains a "c"))
(assert (>= (str.len a) 2))
;(check-sat)
(pop)

;(push)
;(set-info :status sat)
;(assert (str.contains a b))
;(assert (not (str.contains b c)))
;(assert (str.contains a c))
;(check-sat)
;(pop)


;(push)
;(set-info :status sat)
;(assert (str.contains a b))
;(assert (not (str.contains b c)))
;(assert (not (str.contains a c)))
;(check-sat)
;(pop)

;(push)
;(set-info :status unsat)
;(assert (str.contains a b))
;(assert (str.contains b c))
;(assert (not (str.contains a c)))
;(check-sat)
;o(pop)



(push)
(set-info :status sat)
(assert (str.contains "abc" a))
(assert (str.contains "bcd" a))
(check-sat)
(pop)


(push)
(set-info :status sat)
(assert (str.contains "abc" a))
(assert (str.contains "bcd" a))
(assert (>= (str.len a) 1))
(check-sat)
(pop)

(push)
(set-info :status sat)
(assert (str.contains "abc" a))
(assert (str.contains "bcd" a))
(assert (>= (str.len a) 2))
(check-sat)
(pop)


(push)
(set-info :status unsat)
(assert (str.contains "abc" a))
(assert (str.contains "bcd" a))
(assert (>= (str.len a) 3))
(check-sat)
(pop)


(push)
(set-info :status unsat)
(assert (str.contains "abc" a))
(assert (str.contains "def" a))
(assert (not (= a "")))
(check-sat)
(pop)


(simplify (= 0  (str.indexof "abc" "a")))
(simplify (= 1  (str.indexof "abc" "b")))
(simplify (= 2  (str.indexof "abc" "c")))
(simplify (= -1 (str.indexof "abc" "d")))
(simplify (= 2  (str.indexof "abc" "c" 1)))
(simplify (= 1  (str.indexof "abc" "b" 1)))
(simplify (= -1 (str.indexof "abc" "b" 2)))

(push)
(set-info :status sat)
(assert (= (str.len a) (+ 3 (str.indexof a "abc"))))
(check-sat)
(pop)

(push)
(set-info :status sat)
(assert (= (str.len a) (+ 3 (str.indexof a "abc"))))
(assert (= (str.len a) 4))
(check-sat)
(pop)

(push)
(set-info :status unsat)
(assert (= (str.len a) (+ 3 (str.indexof a "abc"))))
(assert (not (= -1 (str.indexof a "abc"))))
(assert (= (str.len a) 2))
(check-sat)
(pop)

(push)
(set-info :status sat)
(assert (= (str.len a) (+ 3 (str.indexof a "abc"))))
(assert (= (str.len a) 3))
(check-sat)
(get-model)
(pop)

(push)
(set-info :status unsat)
(assert (= (str.len a) (+ 3 (str.indexof a "abc"))))
(assert (= (str.len a) 3))
(assert (not (= a "abc")))
(check-sat)
(pop)

(push)
(set-info :status sat)
(assert (= (str.len a) (+ 3 (str.indexof a "abc"))))
(assert (not (= -1 (str.indexof a "abc"))))
(assert (not (= a "abc")))
(check-sat)
(pop)



(push)
(set-info :status sat)
(assert (not (= -1 (str.indexof a "abc"))))
;(assert (not (str.suffixof "abc" a)))
(assert (not (str.prefixof "abc" a)))
(check-sat)
(pop)

(push)
(set-info :status sat)
(assert (= (str.len (str.++ a a)) (+ 3 (str.indexof a "abc"))))
(check-sat)
(pop)



; suffix/prefix
(push)
(set-info :status unsat)
(assert (str.suffixof a b))
(assert (str.suffixof b c))
(assert (not (str.suffixof a c)))
(check-sat)
(pop)

(push)
(set-info :status unsat)
(assert (str.prefixof a b))
(assert (str.prefixof b c))
(assert (not (str.prefixof a c)))
(check-sat)
(pop)

(push)
(set-info :status sat)
(assert (str.prefixof a b))
(assert (str.prefixof a c))
(assert (not (str.prefixof b c)))
(assert (not (str.prefixof c b)))
(check-sat)
(pop)


; length
(push)
(set-info :status sat)
(assert (= a "abcde"))
(assert (<= (str.len a) 5))
(check-sat)
(pop)


(push)
(set-info :status unsat)
(assert (= a "abcde"))
(assert (<= (str.len a) 4))
(check-sat)
(pop)

(push)
(set-info :status sat)
(assert (= a "abcde"))
(assert (<= (str.len a) 5))
(check-sat)
(pop)

(push)
(set-info :status sat)
(assert (= (str.++ a b) "abcde"))
(assert (<= (str.len a) 3))
(assert (<= (str.len b) 2))
(check-sat)
(get-model)
(pop)

(push)
(set-info :status unsat)
(assert (= (str.++ a b) "abcde"))
(assert (<= (str.len a) 2))
(assert (<= (str.len b) 2))
(check-sat)
(pop)

(push)
(set-info :status unsat)
(assert (= (str.++ a b) "abcde"))
(assert (<= (str.len a) 3))
(assert (<= (str.len b) 1))
(check-sat)
(pop)

(push)
(set-info :status sat)
(assert (= (str.++ a b) "abcde"))
(assert (= (str.len a) 3))
(check-sat)
(get-model)
(pop)


; replace

(simplify (str.replace "ab" "a" "A"))
(push)
(set-info :status sat)
(assert (= (str.replace "ab" "a" "A") "Ab"))
(check-sat)
(pop)

(push)
(set-info :status unsat)
(assert (= (str.replace "ab" "a" "A") "bb"))
(check-sat)
(pop)

(push)
(set-info :status sat)
(assert (or (= c "a") (= c "b")))
(assert (= (str.replace "ab" c "A") "Ab"))
(check-sat)
(pop)


(push)
(set-info :status unsat)
(assert (or (= c "c") (= c "b")))
(assert (= (str.replace "ab" c "A") "Ab"))
(check-sat)
(pop)

(exit)

(push)
(set-info :status sat)
(assert (= "ab" (str.replace a "yyy" "ab")))
(check-sat)
(pop)



(push)
(set-info :status sat)
(assert (= "ab" (str.replace a "yyy" "abb")))
(check-sat)
(get-model)
(pop)

; TBD: 

; unknown
(push)
(set-info :status sat)
(assert (str.suffixof a b))
(assert (str.suffixof a c))
(assert (not (str.suffixof b c)))
(assert (not (str.suffixof c b)))
(check-sat)
(pop)

; wrong model
(push)
(set-info :status sat)
(assert (= "ab" (str.replace a "ab" "")))
(check-sat)
;(get-model)
(pop)


; wrong model
(push)
(set-info :status sat)
(assert (= (str.len a) (+ (str.len b) (str.indexof a b))))
(assert (not (= -1 (str.indexof a b))))
(check-sat)
;(get-model)
(pop)


; slow:
(push)
(set-info :status sat)
(assert (= (str.len a) (+ 3 (str.indexof a "abc"))))
(assert (not (= -1 (str.indexof a "abc"))))
(assert (not (str.suffixof a "abc")))
;(check-sat)
;(get-model)
(pop)

; diverges
(push)
(set-info :status sat)
(assert (not (= -1 (str.indexof a "abc"))))
(assert (not (str.suffixof "abc" a)))
(assert (not (str.prefixof "abc" a)))
;(check-sat)
(pop)

; diverges
(push)
(set-info :status unsat)
(assert (= (str.len a) (+ (str.len b) (str.indexof a b))))
(assert (not (= -1 (str.indexof a b))))
(assert (not (str.suffixof b a)))
;(check-sat)
(pop)
