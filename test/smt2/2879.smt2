(declare-fun undef!5 () (_ BitVec 4))
(declare-fun undef!3 () (_ BitVec 4))
(assert (forall ((undef!0 (_ BitVec 4)) (undef!2 (_ BitVec 4)))
             (let ((a!1 (= (bvxor (bvnot ((_ extract 0 0) undef!0))
                                     ((_ extract 0 0) undef!2))
                              (bvxor #b1
                                     ((_ extract 0 0) undef!3)
                                     ((_ extract 0 0) undef!5)))))
                  (not (and a!1
                            (= ((_ extract 3 1) undef!2)
                               ((_ extract 3 1) undef!5)))))))
(check-sat)
