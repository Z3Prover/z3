(set-option :model_validate true)
(set-option :model true)
(declare-const v0 Bool)
(declare-const v1 Bool)
(declare-const v2 Bool)
(declare-const v3 Bool)
(declare-const v4 Bool)
(declare-const v5 Bool)
(declare-const i2 Int)
(declare-const i4 Int)
(declare-const i6 Int)
(declare-const i7 Int)
(declare-const i8 Int)
(declare-const i11 Int)
(declare-const i13 Int)
(declare-const i14 Int)
(declare-const i15 Int)
(declare-const i16 Int)
(declare-const i17 Int)
(declare-const v6 Bool)
(declare-const i18 Int)
(declare-const v7 Bool)
(assert (or (> i15 i13) v1))
(assert (or (> i15 i13) (distinct 256 27)))
(assert (or (>= i6 40) v5))
(assert (or v5 v2 v0 v2 (distinct 256 27)))
(assert (or v0 v1))
(assert (or v1 (distinct 256 27) v5))
(assert-soft (or (or v2 (distinct i4 40) (distinct i4 40) v0 v0 v1 v0 v0 (distinct i4 40) v0 v5) (xor (or v2 (distinct i4 40) (distinct i4 40) v0 v0 v1 v0 v0 (distinct i4 40) v0 v5) v4 v2) (or v2 (distinct i4 40) (distinct i4 40) v0 v0 v1 v0 v0 (distinct i4 40) v0 v5)))
(assert-soft (or v1))
(assert-soft (or (> i15 i13)))
(assert (or v5 v5 (distinct i4 40) (>= i6 40)))
(assert (or (>= i6 40)))
(assert (or (distinct 256 27) (> i15 i13) v0 (distinct i4 40) (> i15 i13) v2 (or v2 (distinct i4 40) (distinct i4 40) v0 v0 v1 v0 v0 (distinct i4 40) v0 v5)))
(assert (or (xor (or v2 (distinct i4 40) (distinct i4 40) v0 v0 v1 v0 v0 (distinct i4 40) v0 v5) v4 v2)))
(assert (or v2 v5))
(assert (or (or v2 (distinct i4 40) (distinct i4 40) v0 v0 v1 v0 v0 (distinct i4 40) v0 v5) (or v2 (distinct i4 40) (distinct i4 40) v0 v0 v1 v0 v0 (distinct i4 40) v0 v5)))
(assert (or (distinct i4 40) (distinct 256 27) (>= i6 40)))
(assert-soft (or (> i15 i13) (distinct 256 27)))
(assert (or (>= i6 40) (distinct i4 40) (distinct 256 27) (> i15 i13) v0))
(assert (or (distinct i4 40)))
(assert (or (> i15 i13) (distinct i4 40)))
(assert-soft (or v0 (xor (or v2 (distinct i4 40) (distinct i4 40) v0 v0 v1 v0 v0 (distinct i4 40) v0 v5) v4 v2)))
(assert (or v2 (> i15 i13) v1 v2))
(assert (or (distinct 256 27) (or v2 (distinct i4 40) (distinct i4 40) v0 v0 v1 v0 v0 (distinct i4 40) v0 v5) (distinct i4 40) (> i15 i13) v2 v0 (> i15 i13)))
(assert (or (distinct 256 27)))
(assert (or (or v2 (distinct i4 40) (distinct i4 40) v0 v0 v1 v0 v0 (distinct i4 40) v0 v5) (> i15 i13) v5 (distinct i4 40) v2 (xor (or v2 (distinct i4 40) (distinct i4 40) v0 v0 v1 v0 v0 (distinct i4 40) v0 v5) v4 v2)))
(assert-soft (or v1))
(assert (or v2 (distinct i4 40) v0))
(assert (or (> i15 i13) v5 v0 v0 v2 v1 (or v2 (distinct i4 40) (distinct i4 40) v0 v0 v1 v0 v0 (distinct i4 40) v0 v5) v0 (> i15 i13) (>= i6 40) (distinct i4 40) (distinct 256 27) (>= i6 40) v0))
(check-sat)
(exit)
