; origin: handwritten/generated (C. Eisenhofer) : hard_cyclic_14_ring_buffer.smt2
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)

(define-fun abc () (RegEx String) (str.to_re "abc"))
(define-fun bca () (RegEx String) (str.to_re "bca"))

(define-fun R-abc () (RegEx String) (re.* abc))
(define-fun R-bca () (RegEx String) (re.* bca))

(assert (str.in_re (str.++ x y x y) R-abc))
(assert (str.in_re (str.++ y x y x) R-bca))

;; The "Ring Buffer Overlap"
;; `xyxy` belongs to (abc)* and `yxyx` belongs to (bca)*.
;; We add a literal to ensure one frame breaks the parity unless lengths perfectly align. 
(assert (str.in_re (str.++ x "a" y) R-abc))
(assert (str.in_re (str.++ y "b" x) R-bca))

;; The unwinder sees multiple variables that are completely dependent on each other's cycles.
;; `x` and `y` swap positions across regexes with shifted states. 
(check-sat)