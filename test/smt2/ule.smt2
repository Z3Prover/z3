(declare-const X (_ BitVec 4))

(set-option :model_validate true)
(define-fun a () Bool (bvule #x2 (bvadd #x4 X)))
(define-fun b () Bool (bvule #x8 (bvadd #x4 X)))
(define-fun c () Bool (bvule #x4 (bvadd #x4 X)))

(define-fun x () Bool (or (bvule X #xb) (bvule #xe X)))
(define-fun y () Bool (and (bvule X #xb) (bvule #x4 X)))
(define-fun z () Bool (bvule X #xb))


(push)
(assert (not (= x a)))
(check-sat)
(pop)

(push)
(assert (not (= y b)))
(check-sat)
(pop)

(push)
(assert (not (= z c)))
(check-sat)
(pop)