;   File name:    bubble_sort.smt2
; 
;   BUBBLESORT  -  Copyright (c) March, 2021 - Matteo Nicoli
;
;   An example of bounded model checking of the classic bubble sort algorithm.
;   we will copy the array values into a list in order to check whether the 
;   array is ordered or not. That's because:
;       - it's easier to walk recursively through a list
;       - it gives an example of how list and sequences work in Z3
;


; size of the array
(declare-const dim Int)

; arrays declaration
(declare-const A0 (Array Int Int))
(declare-const A1 (Array Int Int))
(declare-const A2 (Array Int Int))
(declare-const A3 (Array Int Int))

; indexes declaration
(declare-const i0 Int)
(declare-const i1 Int)
(declare-const i2 Int)
(declare-const i3 Int)

(declare-const j0 Int)
(declare-const j1 Int)
(declare-const j2 Int)
(declare-const j3 Int)

(declare-const tmp0 Int)
(declare-const tmp1 Int)
(declare-const tmp2 Int)

; lists declaration (for post condition)
(declare-const l0 (List Int))
(declare-const l1 (List Int))
(declare-const l2 (List Int))
(declare-const l3 (List Int))
(declare-const l4 (List Int))

(define-fun init_indexes ((_i Int) (_j Int)) Bool
    (and
        (= _i 0)
        (= _j 0)
    )
)

(define-fun inner_loop 
                        (
                            (_A0 (Array Int Int))
                            (_A1 (Array Int Int))
                            (tmp Int)
                            (_i0 Int)
                            (_dim Int)
                        ) Bool
    (ite
        (> (select _A0 _i0) (select _A0 (+ _i0 1)))
        (and
            (= tmp (select _A0 _i0))
            (= _A1 (store _A0 _i0 (select _A0 (+ _i0 1))))
            (= _A1 (store _A0 (+ _i0 1) tmp))
        )
        (= _A1 _A0)
    )
)

; the body of the bubblesort algorithm
(define-fun bsort_step 
                        (
                            (_A0 (Array Int Int))
                            (_A1 (Array Int Int))
                            (tmp Int)
                            (_i0 Int)
                            (_j0 Int)
                            (_i1 Int)
                            (_j1 Int)
                            (_dim Int)
                        ) Bool
    (ite
        (< _j0 (- _dim 1))
        (and 
            (ite 
                (< _i0 (- _dim 1))
                (and
                    (inner_loop _A0 _A1 tmp _i0 _dim)
                    (= _i1 (+ _i0 1))
                )
                (= _j1 (+ _j0 1))
            )
            (= _j1 (+ _j0 1))
        )
        (and
            (= _j1 (+ _j0 1))
            (= _A1 _A0)
        )
    )
)

; the function by which we check whether the list is ordered
(define-fun-rec check ((_l (List Int))) Bool
    (ite 
        (= _l nil)
        true
        (ite
            (not (= (tail _l) nil))
            (and
                (>= (head _l) (head (tail _l)))
                (check (tail _l))
            )
            true
        )
    )
)

; sets the size of the array
(assert (= dim 4))

; initialization of the counters
(assert (init_indexes i0 j0))

; the first step of the sorting algorithm
(assert (bsort_step A0 A1 tmp0 i0 j0 i1 j1 dim))
(assert (bsort_step A1 A2 tmp1 i1 j1 i2 j2 dim))
(assert (bsort_step A2 A3 tmp2 i2 j2 i3 j3 dim))

; filling the list for test
(assert
    (and
        (= l0 nil)
        (= l1 (insert (select A3 0) l0))
        (= l2 (insert (select A3 1) l1))
        (= l3 (insert (select A3 2) l2))
        (= l4 (insert (select A3 3) l3))
    )
)

(echo "BUBBLE SORT")

(push)

; (negated) post-condition
(assert (not (check l4)))

(echo "Testing the validity of the algorithm; `unsat` expected: ")

; `unsat` expected
(check-sat)

(echo "---------------------")

(pop)

; post-condition
(assert (check l4))

(echo "Getting a model; `sat` expected: ")

; `sat` expected
(check-sat)

(echo "---------------------")

(echo "Model: ")
(get-value (A3))
(exit)
