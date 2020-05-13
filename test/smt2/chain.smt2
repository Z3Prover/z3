
; Copyright (c) 2015 Microsoft Corporation


(declare-const a Real)
(declare-const b Real)
(declare-const c Real)

(display (< a b c))
(display (<= a b c))
(display (> a b c))
(display (>= a b c))

(declare-const d Real)

(display (< a b c d))
(display (<= a b c d))
(display (> a b c d))
(display (>= a b c d))

(reset)

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

(display (< a b c))
(display (<= a b c))
(display (> a b c))
(display (>= a b c))

(declare-const d Int)

(display (< a b c d))
(display (<= a b c d))
(display (> a b c d))
(display (>= a b c d))
