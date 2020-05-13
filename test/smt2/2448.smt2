;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                         ;
; some arbitrary sequence ;
;                         ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;
(declare-const A (Seq Int))

;;;;;;;;;;;;;
;           ;
; max index ;
;           ;
;;;;;;;;;;;;;
(declare-const m Int)

;;;;;;;;;;;;;;;;;;;;;;;;;
;                       ;
; max index constraints ;
;                       ;
;;;;;;;;;;;;;;;;;;;;;;;;;
(assert (<= 0 m))
(assert (< m (seq.len A)))
(assert (forall ((i Int)) (<= (seq.nth A i) (seq.nth A m))))

;;;;;;;;;;;;;;;;;;;;;;;;;;
;                        ;
; the projected sequence ;
;                        ;
;;;;;;;;;;;;;;;;;;;;;;;;;;
(declare-const f_A (Seq Int))
(assert 
	(let (
		(max (seq.nth A m))
		(n   (seq.len A)))
	(ite
		(or (>= max n) (< max 0))
		(= f_A (seq.unit 74))
		(= f_A (seq.++
			(seq.extract A 0 m)
			(seq.extract A (+ m 1) (- (- n 1) m)))))))

;(assert (= f_A (seq.unit 74)))

;;;;;;;;;;;;;;;;;
;               ;
; specification ;
;               ;
;;;;;;;;;;;;;;;;;
(define-fun spec ((in (Seq Int))) Bool
	(let (
		(n (seq.len in)))
	(and
		(forall ((j Int))
			(=>
				(and
					(<= 0 j)
					(<  j n))
				(and
					(<= 0 (seq.nth in j))
					(<  (seq.nth in j) n))))))
)

(declare-const j0 Int)
(define-fun specN ((in (Seq Int))) Bool
	(let (
		(n (seq.len in)))
	(not (and
			(=>
				(and
					(<= 0 j0)
					(<  j0 n))
				(and
					(<= 0 (seq.nth in j0))
					(<  (seq.nth in j0) n))))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;
;                        ;
; specification property ;
;                        ;
;;;;;;;;;;;;;;;;;;;;;;;;;;
(assert (spec f_A))
(assert (specN A))

;;;;;;;;;
;       ;
; debug ;
;       ;
;;;;;;;;;
(declare-const spec_f_A Bool)
;(assert (= (spec f_A) spec_f_A))
(assert spec_f_A)

;;;;;;;;;;;;;;;;;;;;;;
;                    ;
; initial conditions ;
;                    ;
;;;;;;;;;;;;;;;;;;;;;;
(assert (< 2 (seq.len A)))
(assert (< (seq.len A) 5))

;;;;;;;;;;;;;;;;;;;;;;;;;
;                       ;
; check sat + get model ;
;                       ;
;;;;;;;;;;;;;;;;;;;;;;;;;
(check-sat)
;(get-model)
