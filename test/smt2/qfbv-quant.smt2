;; Variation of GitHub Issue #544; Nuno wants quantifiers in qfbv
(assert (forall ((X (_ BitVec 32)))
            (exists ((Y (_ BitVec 32)))
                (= X (bvmul Y Y)))))
(apply qfbv)
