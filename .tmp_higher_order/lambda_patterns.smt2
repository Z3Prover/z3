(set-option :global-decls false)
(set-option :smt.mbqi false)
(set-option :auto_config false)
(set-option :produce-unsat-cores true)
(set-option :model true)
(set-option :smt.case_split 3)
(set-option :smt.relevancy 2)
(set-option :rewriter.enable_der false)
(set-option :rewriter.sort_disjunctions false)
(set-option :pi.decompose_patterns false)
(set-option :smt.arith.solver 6)
(set-option :smt.random-seed 0)
(declare-sort Term)
(declare-fun Tm_refine (Term (=> Term Bool)) Term)
(declare-fun HasType (Term Term) Bool)
(declare-fun Int_term () Term)
(declare-fun Unbox_int (Term) Int)

; (assert (! (forall ((x Term) (base Term) (refine (=> Term Bool)))
;             (! (iff (HasType x (Tm_refine base refine))
;                     (and
;                         (HasType x base)
;                         (refine x)))
;                 :pattern ((HasType x (Tm_refine base refine)))
;                 :qid refine_elim_generic.1))
;             :named refine_elim_generic))



(assert (! (forall ((x Term) (y Term))
                (! (implies 
                    (HasType x (Tm_refine Int_term (lambda ((x Term)) (>= (Unbox_int x) (Unbox_int y)))))
                    (HasType x Int_term))
                :pattern 
                    ((HasType x (Tm_refine Int_term (lambda ((x Term)) (>= (Unbox_int x) (Unbox_int y))))))
                :qid refine_int_elim.1
                ))
                :named refine_int_elim))

(define-fun Bounded_int_term ((y Term)) Term
    (Tm_refine Int_term (lambda ((x Term)) (>= (Unbox_int x) (Unbox_int y)))))
                    

(assert (not (forall ((x Term) (y Term)) (implies (HasType x (Bounded_int_term y)) (HasType x Int_term)))))
(check-sat)
(get-unsat-core)