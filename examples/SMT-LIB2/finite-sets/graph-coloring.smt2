; taken from https://st.fyi/posts/z3finitesets/
(define-const colors (FiniteSet Int) (set.range 1 3))

(declare-const v1 Int)
(declare-const v2 Int)
(declare-const v3 Int)

(assert (set.in v1 colors))
(assert (set.in v2 colors))
(assert (set.in v3 colors))

; adjacent vertices differ
(assert (not (= v1 v2)))
(assert (not (= v2 v3)))
(assert (not (= v1 v3)))

(check-sat)