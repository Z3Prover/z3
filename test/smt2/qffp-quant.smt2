;; GitHub Issue #544
(set-option :smt.mbqi.max_iterations 10)

(assert (forall ((%rundef0 (_ FloatingPoint 11 53)))
            (fp.isNaN %rundef0)))
(apply qffp)
