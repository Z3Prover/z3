(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(declare-fun d () Real)
(declare-fun e () Real)
(declare-fun f () Real)
(declare-fun g () Real)
(declare-fun h () Real)
(declare-fun i () Real)
(declare-fun j () Real)
(declare-fun k () Real)
;(declare-fun cj () Real)
;(declare-fun ck () Real)
;(declare-fun bi () Real)

;  (define-fun a () Real (- 1.0))
;  (define-fun b () Real  (- 1.0))
;  (define-fun c () Real (/ 1.0 16.0))
;  (define-fun d () Real  0.0)
;  (define-fun e () Real  0.0)
;  (define-fun f () Real  (- 1.0))

;  (define-fun k () Real (- (/ 1.0 4.0)))
;  (define-fun j () Real (- (/ 1.0 4.0)))
;  (define-fun i () Real  (- 1.0))
;  (define-fun h () Real  1.0)
;  (define-fun g () Real  0.0)

(define-fun cj () Real (/ c j))
(define-fun ck () Real (/ c k))
(define-fun bi () Real (/ b i))


(assert
  (not
    (exists
      ((l Real))
      (=>
        (and
          (=
            (<= 0 l)
            (>= (+ (* e l) cj) 0)
          )
          (>= bi 0)
        )
        (<=
          (- d g)
          (*
            (/ 1 2)
            (+
              (* e (* bi bi))
              (* (* 2 bi) k)
              (* 2 (- d g))
            )
          )
        )
      )
    )
  )
)
(assert (= h (/ a e) (* f f)))
(assert (= k cj ck))
(check-sat)
;(get-model)

(exit)
