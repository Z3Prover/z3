;   File name:    loop_unrolling_bitvec.smt2
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
;   We define our custom sort `IntValue` that represents a 32-bit integer value.


(define-sort IntValue () (_ BitVec 32))
(declare-const x IntValue)
(declare-const A (Array IntValue IntValue))
(declare-const i_0 IntValue)
(declare-const found_0 IntValue)

(declare-const found_1 IntValue)
(declare-const found_2 IntValue)
(declare-const i_1 IntValue)
(declare-const i_2 IntValue)

; Pre-condition: variables initialization
(assert
    (and
        (= i_0 #x00000000)
        (= found_0 #x00000000)
    )
)

; Transition function
(define-fun body ((f_0 IntValue) (f IntValue) (i_0 IntValue) (i_1 IntValue)(_A (Array IntValue IntValue)) (_x IntValue)) Bool
    (and
        (= f (ite (= _x (select _A i_0)) #x00000001 f_0))
        (= i_1 (bvadd i_0 #x00000001))
    )
)

; Post-condition function
(define-fun post ((_f IntValue) (_i IntValue) (_x IntValue) (_A (Array IntValue IntValue))) Bool
    (=
        (= _f #x00000001)
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
