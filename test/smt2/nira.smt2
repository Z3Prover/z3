
; Copyright (c) 2015 Microsoft Corporation

(declare-const x Real)

(assert (> x 0))

(apply (then simplify (when is-nra (echo "nra"))) :print false)
(apply (then simplify (when is-lra (echo "lra"))) :print false)
(apply (then simplify (when is-nia (echo "nia"))) :print false)
(apply (then simplify (when is-lia (echo "lia"))) :print false)
(apply (then simplify (when is-lira (echo "lira"))) :print false)
(apply (then simplify (when is-nira (echo "nira"))) :print false)

(assert (= (^ x 2.0) 2))

(echo "---------------")

(apply (then simplify (when is-nra (echo "nra"))) :print false)
(apply (then simplify (when is-lra (echo "lra"))) :print false)
(apply (then simplify (when is-nia (echo "nia"))) :print false)
(apply (then simplify (when is-lia (echo "lia"))) :print false)
(apply (then simplify (when is-lira (echo "lira"))) :print false)
(apply (then simplify (when is-nira (echo "nira"))) :print false)

(declare-const y Int)

(assert (= x y))

(echo "---------------")

(apply (then simplify (when is-nra (echo "nra"))) :print false)
(apply (then simplify (when is-lra (echo "lra"))) :print false)
(apply (then simplify (when is-nia (echo "nia"))) :print false)
(apply (then simplify (when is-lia (echo "lia"))) :print false)
(apply (then simplify (when is-lira (echo "lira"))) :print false)
(apply (then simplify (when is-nira (echo "nira"))) :print false)

(reset)

(declare-const y Int)
(assert (> y 0))

(echo "---------------")

(apply (then simplify (when is-nra (echo "nra"))) :print false)
(apply (then simplify (when is-lra (echo "lra"))) :print false)
(apply (then simplify (when is-nia (echo "nia"))) :print false)
(apply (then simplify (when is-lia (echo "lia"))) :print false)
(apply (then simplify (when is-lira (echo "lira"))) :print false)
(apply (then simplify (when is-nira (echo "nira"))) :print false)

(assert (= (* y y) 4.0))

(echo "---------------")

(apply (then simplify (when is-nra (echo "nra"))) :print false)
(apply (then simplify (when is-lra (echo "lra"))) :print false)
(apply (then simplify (when is-nia (echo "nia"))) :print false)
(apply (then simplify (when is-lia (echo "lia"))) :print false)
(apply (then simplify (when is-lira (echo "lira"))) :print false)
(apply (then simplify (when is-nira (echo "nira"))) :print false)

(assert (forall ((x Int)) (exists ((y Int)) (> y x))))

(echo "---------------")

(apply (then simplify (when is-nra (echo "nra"))) :print false)
(apply (then simplify (when is-lra (echo "lra"))) :print false)
(apply (then simplify (when is-nia (echo "nia"))) :print false)
(apply (then simplify (when is-lia (echo "lia"))) :print false)
(apply (then simplify (when is-lira (echo "lira"))) :print false)
(apply (then simplify (when is-nira (echo "nira"))) :print false)

(declare-const x Real)
(assert (> x 0))

(echo "---------------")

(apply (then simplify (when is-nra (echo "nra"))) :print false)
(apply (then simplify (when is-lra (echo "lra"))) :print false)
(apply (then simplify (when is-nia (echo "nia"))) :print false)
(apply (then simplify (when is-lia (echo "lia"))) :print false)
(apply (then simplify (when is-lira (echo "lira"))) :print false)
(apply (then simplify (when is-nira (echo "nira"))) :print false)

(reset)

(echo "---------------")

(assert (forall ((x Int)) (exists ((y Int)) (> y x))))

(apply (then simplify (when is-nra (echo "nra"))) :print false)
(apply (then simplify (when is-lra (echo "lra"))) :print false)
(apply (then simplify (when is-nia (echo "nia"))) :print false)
(apply (then simplify (when is-lia (echo "lia"))) :print false)
(apply (then simplify (when is-lira (echo "lira"))) :print false)
(apply (then simplify (when is-nira (echo "nira"))) :print false)

(reset)

(echo "---------------")

(assert (forall ((x Real)) (exists ((y Real)) (> y x))))

(apply (then simplify (when is-nra (echo "nra"))) :print false)
(apply (then simplify (when is-lra (echo "lra"))) :print false)
(apply (then simplify (when is-nia (echo "nia"))) :print false)
(apply (then simplify (when is-lia (echo "lia"))) :print false)
(apply (then simplify (when is-lira (echo "lira"))) :print false)
(apply (then simplify (when is-nira (echo "nira"))) :print false)

