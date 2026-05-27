; Z3 invocation started by F*
; F* version: 2025.10.06~dev -- commit hash: 09918f026ec154eaad0c4934fa0cd34dd564a1e8
; Z3 version (according to F*): 4.13.3

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
(declare-datatypes () ((Universe 
(Univ (ulevel Int)))))
(declare-datatypes () ((Fuel 
(ZFuel) 
(SFuel (prec Fuel)))))
(declare-fun MaxIFuel () Fuel)
(declare-fun MaxFuel () Fuel)
(declare-fun Valid (Term) Bool)
(declare-fun HasTypeFuel (Fuel Term Term) Bool)
(define-fun HasTypeZ ((x Term) (t Term)) Bool
(HasTypeFuel ZFuel x t))
(define-fun HasType ((x Term) (t Term)) Bool
(HasTypeFuel MaxIFuel x t))

(declare-fun ApplyTT (Term Term) Term)
(declare-fun Tm_lambda (Term (=> Term Term)) Term)
(declare-fun Prims.l_Forall (Universe Term Term) Term)
(push) ;; push{1
(declare-fun uu___44 () Universe)
(push) ;; push{0
(assert
 (not (forall ((@x0 Term) (@x1 Term) (post Term))
        (implies
          (forall ((res Term))
            (! (implies 
                (HasType
                  res 
                  (Prims.l_Forall uu___44 @x0
                    (Tm_lambda
                        @x0
                        (lambda ((@x4 Term)) (ApplyTT @x1 @x4))

                    ; (Tm_lambda
                    ;     @x0
                    ;     (lambda ((@x6 Term)) (ApplyTT @x1 @x6))

                        )))
                (Valid (ApplyTT post res)))
              :pattern ((Valid (ApplyTT post res)))))
          (forall ((@x5 Term))
            (implies
              (HasType
                @x5
                (Prims.l_Forall
                  uu___44
                  @x0
                  (Tm_lambda
                    @x0
                    (lambda ((@x6 Term)) (ApplyTT @x1 @x6)))))
              (Valid
                (ApplyTT post @x5))))))))

        
(set-option :rlimit 2500000)
(check-sat)
(pop) ;; 0}pop

; QUERY ID: (FStar.Classical.get_forall, 1)
; STATUS: unknown because (incomplete (theory array))
