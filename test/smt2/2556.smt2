(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(declare-fun d () Real)
(declare-fun f () Real)
(declare-fun e () Real)
(declare-fun g () Real)
(declare-fun j () Real)
(declare-fun k () Real)
(declare-fun h () Real)
(declare-fun m () Real)
(declare-fun i () Real)
(assert
  (not
    (exists
      ((l Real))
      (=>
        (and
          (=> (<= 0 l) (< l g (* e l) 0))
          (>= (/ c m) 0)
        )
        (<=
          (- f k)
          (*
            (/ 1 2)
            (+
              (* (* 2 (/ c m)) j)
              (* 2 (- f k))
            )
          )
        )
      )
    )
  )
)
(assert (= h (/ a e) (* b h)))
(assert (= h (/ b g) (/ c m)))
(assert (= j (/ d i)))
(assert (= i (/ d j)))
(check-sat)
;(get-model)