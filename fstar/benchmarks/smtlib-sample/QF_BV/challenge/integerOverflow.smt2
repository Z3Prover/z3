(set-info :smt-lib-version 2.6)
;; Check whether an integer overflow can occur in the multiplication
;; given that the division does not crash the process:
;; int baz(int x, int y)
;; { return (x / y) * y; }

(set-logic QF_BV)
(set-info :category "industrial")
(set-info :source |GrammaTech| )
(set-info :status unsat)
(declare-fun y () (_ BitVec 32) )
(define-fun tmp!40 () Bool (= #x00000000 y))
(define-fun tmp!41 () Bool (not tmp!40)) ; check for division by zero
(assert tmp!41)
(define-fun tmp!43 () Bool (= #xffffffff y))
(declare-fun x () (_ BitVec 32) )
(define-fun tmp!42 () Bool (= #x80000000 x))
(define-fun tmp!44 () Bool (and tmp!43 tmp!42))
(define-fun tmp!45 () Bool (not tmp!44)) ; check for division overflow (trap on x86)
(assert tmp!45)
(define-fun tmp!39 () (_ BitVec 32) (bvsdiv x y)) ; x / y
(define-fun tmp!47 () (_ BitVec 64) ((_ sign_extend 32) tmp!39))
(define-fun tmp!48 () (_ BitVec 64) ((_ sign_extend 32) y))
(define-fun tmp!49 () (_ BitVec 64) (bvmul tmp!47 tmp!48))
(define-fun tmp!50 () (_ BitVec 33) ((_ extract 63 31) tmp!49))
(define-fun tmp!54 () Bool (= #b000000000000000000000000000000000 tmp!50))
(define-fun tmp!55 () Bool (not tmp!54))
(define-fun tmp!51 () (_ BitVec 33) (bvnot tmp!50))
(define-fun tmp!52 () Bool (= #b000000000000000000000000000000000 tmp!51))
(define-fun tmp!53 () Bool (not tmp!52))
(define-fun tmp!56 () Bool (and tmp!55 tmp!53)) ; overflow check for x / y * y
(assert tmp!56)
(check-sat)
(exit)
