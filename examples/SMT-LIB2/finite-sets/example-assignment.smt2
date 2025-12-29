; example due to nikolaj's project page




(declare-const s1 (FiniteSet Int))
(declare-const s2 (FiniteSet Int))
(declare-const s3 (FiniteSet Int))
(declare-const s4 (FiniteSet Int))
(declare-const s5 (FiniteSet Int))
(declare-const s6 (FiniteSet Int))
(declare-const s7 (FiniteSet Int))
(declare-const s8 (FiniteSet Int))
(declare-const s9 (FiniteSet Int))

(declare-const t1 (FiniteSet Int))
(declare-const t2 (FiniteSet Int))
(declare-const t3 (FiniteSet Int))
(declare-const t4 (FiniteSet Int))
(declare-const t5 (FiniteSet Int))
(declare-const t6 (FiniteSet Int))
(declare-const t7 (FiniteSet Int))
(declare-const t8 (FiniteSet Int))

(declare-const u1 (FiniteSet Int))
(declare-const u2 (FiniteSet Int))
(declare-const u3 (FiniteSet Int))
(declare-const u4 (FiniteSet Int))
(declare-const u5 (FiniteSet Int))
(declare-const u6 (FiniteSet Int))
(declare-const u7 (FiniteSet Int))
(declare-const u8 (FiniteSet Int))

(assert (or (set.subset s1 t1) (set.subset s1 u1)))

(assert (set.subset t1 s2))
(assert (set.subset u1 s2))

(assert (or (set.subset s2 t2) (set.subset s2 u2)))

(assert (set.subset t2 s3))
(assert (set.subset u2 s3))

(assert (or (set.subset s3 t3) (set.subset s3 u3)))

(assert (set.subset t3 s4))
(assert (set.subset u3 s4))

(assert (or (set.subset s4 t4) (set.subset s4 u4)))

(assert (set.subset t4 s5))
(assert (set.subset u4 s5))

(assert (or (set.subset s5 t5) (set.subset s5 u5)))

(assert (set.subset t5 s6))
(assert (set.subset u5 s6))

(assert (or (set.subset s6 t6) (set.subset s6 u6)))

(assert (set.subset t6 s7))
(assert (set.subset u6 s7))

(assert (or (set.subset s7 t7) (set.subset s7 u7)))

(assert (set.subset t7 s8))
(assert (set.subset u7 s8))

(assert (or (set.subset s8 t8) (set.subset s8 u8)))

(assert (set.subset t8 s9))
(assert (set.subset u8 s9))

(assert (not (set.subset s1 s9)))


(check-sat)