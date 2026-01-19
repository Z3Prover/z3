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

(declare-const s1prime (FiniteSet Int))
(declare-const s2prime (FiniteSet Int))
(declare-const s3prime (FiniteSet Int))
(declare-const s4prime (FiniteSet Int))
(declare-const s5prime (FiniteSet Int))
(declare-const s6prime (FiniteSet Int))
(declare-const s7prime (FiniteSet Int))
(declare-const s8prime (FiniteSet Int))
(declare-const s9prime (FiniteSet Int))


(declare-const t1 (FiniteSet Int))
(declare-const t2 (FiniteSet Int))
(declare-const t3 (FiniteSet Int))
(declare-const t4 (FiniteSet Int))
(declare-const t5 (FiniteSet Int))
(declare-const t6 (FiniteSet Int))
(declare-const t7 (FiniteSet Int))
(declare-const t8 (FiniteSet Int))

(declare-const t1prime (FiniteSet Int))
(declare-const t2prime (FiniteSet Int))
(declare-const t3prime (FiniteSet Int))
(declare-const t4prime (FiniteSet Int))
(declare-const t5prime (FiniteSet Int))
(declare-const t6prime (FiniteSet Int))
(declare-const t7prime (FiniteSet Int))
(declare-const t8prime (FiniteSet Int))

(declare-const u1 (FiniteSet Int))
(declare-const u2 (FiniteSet Int))
(declare-const u3 (FiniteSet Int))
(declare-const u4 (FiniteSet Int))
(declare-const u5 (FiniteSet Int))
(declare-const u6 (FiniteSet Int))
(declare-const u7 (FiniteSet Int))
(declare-const u8 (FiniteSet Int))

(declare-const u1prime (FiniteSet Int))
(declare-const u2prime (FiniteSet Int))
(declare-const u3prime (FiniteSet Int))
(declare-const u4prime (FiniteSet Int))
(declare-const u5prime (FiniteSet Int))
(declare-const u6prime (FiniteSet Int))
(declare-const u7prime (FiniteSet Int))
(declare-const u8prime (FiniteSet Int))

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

; link
(assert (set.subset s9 s1prime))

; prime part
(assert (or (set.subset s1prime t1prime) (set.subset s1prime u1prime)))

(assert (set.subset t1prime s2prime))
(assert (set.subset u1prime s2prime))

(assert (or (set.subset s2prime t2prime) (set.subset s2prime u2prime)))

(assert (set.subset t2prime s3prime))
(assert (set.subset u2prime s3prime))

(assert (or (set.subset s3prime t3prime) (set.subset s3prime u3prime)))

(assert (set.subset t3prime s4prime))
(assert (set.subset u3prime s4prime))

(assert (or (set.subset s4prime t4prime) (set.subset s4prime u4prime)))

(assert (set.subset t4prime s5prime))
(assert (set.subset u4prime s5prime))

(assert (or (set.subset s5prime t5prime) (set.subset s5prime u5prime)))

(assert (set.subset t5prime s6prime))
(assert (set.subset u5prime s6prime))

(assert (or (set.subset s6prime t6prime) (set.subset s6prime u6prime)))

(assert (set.subset t6prime s7prime))
(assert (set.subset u6prime s7prime))

(assert (or (set.subset s7prime t7prime) (set.subset s7prime u7prime)))

(assert (set.subset t7prime s8prime))
(assert (set.subset u7prime s8prime))

(assert (or (set.subset s8prime t8prime) (set.subset s8prime u8prime)))

(assert (set.subset t8prime s9prime))
(assert (set.subset u8prime s9prime))










(assert (not (set.subset s1 s9prime)))


(check-sat)