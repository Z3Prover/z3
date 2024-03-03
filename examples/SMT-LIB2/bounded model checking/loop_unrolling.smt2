;   File name:    loop_unrolling.smt2
; 
;   Copyright (c) March, 2021 - Matteo Nicoli
;
;
;   Let's start considering a simple C program involving an iteration:
;   
;       #define DIM 2
;       
;       /* uninterpreted functions */
;       long get_number();
;       void fill_array(long *A);
;       
;       int main()
;       {
;           long x = get_number();
;           long A[DIM];
;           long i = 0;
;           long found = 0; 
;           
;           fill_array(A);
;
;           while(i < DIM) {
;               if(x == A[i]) 
;                   found = 1;
;               i++; 
;           }
;       }
;
;   Below, we can see its SSA representation in SMT-LIB2.
;   Our goal is to verify that, at the end of the program, the variable `found`
;   is equal to 1 if, and only if, `x` is an element of the array.


(declare-const x Int)
(declare-const A (Array Int Int))
(declare-const i_0 Int)
(declare-const found_0 Int)

(declare-const found_1 Int)
(declare-const found_2 Int)
(declare-const i_1 Int)
(declare-const i_2 Int)

; Pre-condition: variables initialization
(assert
    (and
        (= i_0 0)
        (= found_0 0)
    )
)

; Transition function
(define-fun body ((f_0 Int) (f Int) (i_0 Int) (i_1 Int)(_A (Array Int Int)) (_x Int)) Bool
    (and
        (= f (ite (= _x (select _A i_0)) 1 f_0))
        (= i_1 (+ i_0 1))
    )
)

; Post-condition function
(define-fun post ((_f Int) (_i Int) (_x Int) (_A (Array Int Int))) Bool
    (=
        (= _f 1)
        (= _x (select _A _i))
    )   
)

; Transition function is called DIM times:
; for practical reasons, we are considering here DIM = 2
(assert (body found_0 found_1 i_0 i_1 A x))
(assert (body found_1 found_2 i_1 i_2 A x))

(push)

(echo "Bounded model checking with loop unrolling")

(echo "------------------------------------------")

; Post-condition (negated) is called DIM times
(assert
    (not
        (or
            (post found_2 i_0 x A)      
            (post found_2 i_1 x A)
        )
    )
)

(echo "Testing the validity of the post-condition: `unsat expected`")

; `unsat` expected
(check-sat)

(pop)

; Post-condition (called DIM times)
(assert
    (or
        (post found_2 i_0 x A)      
        (post found_2 i_1 x A)
    )
)

(echo "Getting a model; `sat` expected: ")

; `sat` expected
(check-sat)

(echo "------------------------------------------")

(echo "Model: ")
(get-value (x A found_2))
(exit)
