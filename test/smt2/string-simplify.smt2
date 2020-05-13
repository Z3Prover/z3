(simplify (str.++ "a" "b"""))        ; "a""b"
(simplify (str.prefixof "a" "b"))      ; false
(simplify (str.prefixof "ab" "abc"))   ; true
(simplify (str.suffixof "ab" "abc"))   ; false
(simplify (str.suffixof "bc" "abc"))   ; true
(simplify (str.suffixof "abc" "abc"))  ; true
(simplify (str.prefixof "" ""))        ; true
(simplify (str.prefixof "" "a"))       ; true
(simplify (str.len ""))              ; 0
(simplify (str.len "a"))             ; 1
(simplify (str.len "ab"))            ; 2
(simplify (str.substr "abc" 1 1))    ; "b"
(simplify (str.substr "abc" 1 2))    ; "bc"
(simplify (str.substr "abc" 1 3))    ; "bc"
(simplify (str.substr "abc" 2 1))    ; "c"
(simplify (str.substr "abc" 3 1))    ; ""
(simplify (str.substr "abc" 4 1))    ; ""
(simplify (str.contains "ab" "abc"))   ; false
(simplify (str.contains "bc" "abc"))   ; false
(simplify (str.contains "abc" "abc"))  ; true
(simplify (str.contains "" ""))        ; true
(simplify (str.contains "a" ""))       ; true
(simplify (str.contains "abb" "abc"))  ; false
(simplify (str.contains "abc" "bc"))   ; true
(simplify (str.contains "abc" "abc"))  ; true
(simplify (str.contains "" ""))        ; true
(simplify (str.contains "" "a"))       ; false
(simplify (str.at "abc" 0))   ; "a"
(simplify (str.at "abc" 1))   ; "b"
(simplify (str.at "abc" 2))   ; "c"
(simplify (str.at "abc" 3))   ; (str.charat "abc" 3)
(simplify (str.replace   "abc" "b" "c")) ; "acc"
(simplify (int.to.str 1))           ; "1"
(simplify (int.to.str 100))         ; "100"
(simplify (str.to.int "1"))         ; 1
(simplify (str.to.int "a"))         ; (str.stoi "a")
(simplify (str.indexof "aabbcc" "b" 1)) ; 1
(simplify (str.indexof "aabbcc" "b" 2)) ; 0
(simplify (str.indexof "aabbcc" "bc" 2)) ; 1
(simplify (str.indexof "aabbcc" "d" 0)) ; (- 1)
(simplify (seq.indexof (seq.++ (seq.unit 0) (seq.unit 1) (seq.unit 2)) (seq.unit 1) 1))

(declare-const a String)
(declare-const b String)
(declare-const c String)

(simplify (str.++ a (str.++ b c))) ; (str.++ (str.++ a b) c)
(simplify (str.++ a ""))            ; a
(simplify (str.++ "" a))            ; a
(simplify (str.++ (str.++ a "a") "b")) ; (str.++ a "ab")
(simplify (str.len (str.++ a "b"))) ; (+ (str.len a) 1)

(simplify (str.prefixof (str.++ a b) a))
(simplify (str.prefixof a (str.++ a b)))
(simplify (str.prefixof (str.++ a b) c))
(simplify (str.prefixof (str.++ a c) (str.++ a b)))
(simplify (str.prefixof "a" (str.++ "b" c)))
(simplify (str.prefixof "a" (str.++ "ab" c)))
(simplify (str.prefixof "ab" (str.++ "a" c)))
(simplify (str.prefixof (str.++ "ab" a) (str.++ "a" c)))

(simplify (str.suffixof (str.++ a b) b ))
(simplify (str.suffixof b (str.++ a b)))
(simplify (str.suffixof (str.++ a b) c))
(simplify (str.suffixof (str.++ c a) (str.++ b a)))
(simplify (str.suffixof (str.++ c "b") "a"))
(simplify (str.suffixof "a" (str.++ c "ba") ))
(simplify (str.suffixof (str.++ c "b") "ab"))
(simplify (str.suffixof (str.++ c "b") (str.++ a "ab")))

(simplify (str.contains a b))
(simplify (str.contains a (str.++ a b c)))
(simplify (str.contains b (str.++ a b c)))
(simplify (str.contains (str.++ a b) (str.++ a b c)))
(simplify (str.contains (str.++ b c) (str.++ a b c)))
(simplify (str.contains (str.++ a c) (str.++ a b c)))

(simplify (str.contains a b))
(simplify (str.contains (str.++ a b c) a))
(simplify (str.contains (str.++ a b c) b))
(simplify (str.contains (str.++ a b c) (str.++ a b)))
(simplify (str.contains (str.++ a b c) (str.++ b c)))
(simplify (str.contains (str.++ a b c) (str.++ a c)))

(simplify (str.replace (str.++ "A" a) "B" b))
(simplify (str.replace (str.++ "AB" a) "B" b))
(simplify (str.replace (str.++ "AB" a) "BA" b))
(simplify (str.replace (str.++ "AB" a) (str.++ "B" a b) c))
