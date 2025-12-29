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
(declare-const s10 (FiniteSet Int))
(declare-const s11 (FiniteSet Int))
(declare-const s12 (FiniteSet Int))
(declare-const s13 (FiniteSet Int))
(declare-const s14 (FiniteSet Int))
(declare-const s15 (FiniteSet Int))
(declare-const s16 (FiniteSet Int))
(declare-const s17 (FiniteSet Int))
(declare-const s18 (FiniteSet Int))
(declare-const s19 (FiniteSet Int))


(assert (set.subset s1 s2))
(assert (set.subset s2 s3))
(assert (set.subset s3 s4))
(assert (set.subset s4 s5))
(assert (set.subset s5 s6))
(assert (set.subset s6 s7))
(assert (set.subset s7 s8))
(assert (set.subset s8 s9))
(assert (set.subset s9 s10))
(assert (set.subset s10 s11))
(assert (set.subset s11 s12))
(assert (set.subset s12 s13))
(assert (set.subset s13 s14))
(assert (set.subset s14 s15))
(assert (set.subset s15 s16))
(assert (set.subset s16 s17))
(assert (set.subset s17 s18))
(assert (set.subset s18 s19))

(assert (not (set.subset s1 s19)))

(check-sat)