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
(define-fun imax ((i Int) (j Int)) Int 
(ite (<= i 0) j 
(ite (<= j 0) i 
(ite (<= i j) j i)))) 
(define-fun U_zero () Universe (Univ 0))
(define-fun U_succ ((u Universe)) Universe
(Univ (+ (ulevel u) 1)))
(declare-fun U_max (Universe Universe) Universe) 
(declare-fun U_unif (Int) Universe)
(declare-fun U_unknown () Universe)
(declare-fun Term_constr_id (Term) Int)
(declare-datatypes () ((Fuel 
(ZFuel) 
(SFuel (prec Fuel)))))
(declare-fun MaxIFuel () Fuel)
(declare-fun MaxFuel () Fuel)
(declare-fun PreType (Term) Term)
(declare-fun Valid (Term) Bool)
(declare-fun HasTypeFuel (Fuel Term Term) Bool)
(define-fun HasTypeZ ((x Term) (t Term)) Bool
(HasTypeFuel ZFuel x t))
(define-fun HasType ((x Term) (t Term)) Bool
(HasTypeFuel MaxIFuel x t))
(declare-fun ApplyTT (Term Term) Term)
(declare-fun Tm_refinement (Term (=> Term Bool)) Term)
(assert (forall ((u Fuel) (x Term) (base Term) (f (=> Term Bool)))
                  (! (iff (and (HasTypeFuel u x base) (select f x))
                          (HasTypeFuel u x (Tm_refinement base f)))
                  :pattern ((HasTypeFuel u x (Tm_refinement base f)))
                  :qid refine_interpretation)))
; (assert (forall ((t Term) (base Term) (f (=> Term Bool)))
;   (! (iff (HasType base t)
;           (HasType (Tm_refinement base f) t))
;   :pattern ((HasType (Tm_refinement base f) t))
;   :qid refine_typing)))
(declare-fun Tm_type (Universe) Term)
(push) ;; push{1
(declare-fun Prims.l_Forall (Universe Term Term) Term)
(declare-fun Prims.l_and (Term Term) Term)
(declare-fun Prims.pure_post (Universe Term) Term)
(declare-fun Prims.pure_post_ (Universe Universe Term Term) Term)
(declare-fun Prims.pure_pre () Term)
(declare-fun Prims.pure_wp_monotonic0 (Universe Term Term) Term)
(declare-fun Tm_refine_d79dab86b7f5fc89b7215ab23d0f2c81 (Universe Term Term) Term)
(declare-fun uu___53 () Universe)
(declare-fun label_1 () Bool)
(declare-fun Tm_abs_25e3493e4b940364e027d68afed2c9f8 (Universe Term Term Term Term) Term)
(declare-fun Tm_abs_f4b968d76e465dbbe733c9606c5bd64d (Universe Term Term Term) Term)

(assert
 (! ;; def=Prims.fst(341,4-341,22); use=Prims.fst(341,4-341,22)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term))
   (! (=
     (Valid (Prims.pure_wp_monotonic0 @u0 @x1 @x2))
     (forall ((@x3 Term) (@x4 Term))
      (! (implies
        (and
         (HasType @x3 (Prims.pure_post @u0 @x1))
         (HasType @x4 (Prims.pure_post @u0 @x1))
         (forall ((@x5 Term))
          (! (implies
            (and
             (HasType @x5 @x1)
             (Valid
              (ApplyTT @x3 @x5)))
            (Valid
             (ApplyTT @x4 @x5)))
           :qid equation_Prims.pure_wp_monotonic0.2))
         (Valid
          (ApplyTT @x2 @x3)))
        (Valid
         (ApplyTT @x2 @x4)))
       :qid equation_Prims.pure_wp_monotonic0.1)))
    :pattern ((Prims.pure_wp_monotonic0 @u0 @x1 @x2))
    :qid equation_Prims.pure_wp_monotonic0))
  :named equation_Prims.pure_wp_monotonic0))
(assert
 (! (forall ((@x0 Term) (@x1 Term))
   (! (iff (and (Valid @x0) (Valid @x1)) (Valid (Prims.l_and @x0 @x1)))
    :pattern ((Prims.l_and @x0 @x1))
    :qid l_and-interp))
  :named l_and-interp))
(push) ;; push{2


; (assert
;  (! ;; def=FStar.Pervasives.fsti(265,46-265,72); use=FStar.Pervasives.fsti(265,46-265,72)
;   (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (f (=> Term bool)))
;    (! (implies
;         (= f (lambda ((x Term)) (Valid @x1)))
;         (iff
;           (Valid
;             (Prims.l_Forall
;             @u0
;             (Tm_refinement @x2 (lambda ((x Term)) (Valid @x1)))
;             (Tm_abs_25e3493e4b940364e027d68afed2c9f8 @u0 @x1 @x2 @x3 @x4)))
;           (forall ((@x5 Term))
;             (! (implies
;               (and
;               (HasType @x5 
;                 (Tm_refinement @x2 (lambda ((@x5 Term)) (Valid @x1)))
;                 )
;               (Valid
;                 (ApplyTT @x3 @x5)))
;               (Valid
;               (ApplyTT @x4 @x5)))
;             :qid l_quant_interp_6bba8ada8d83fbf9a31086f503e84f1b.1))))
;     :pattern
;      ((Valid
;        (Prims.l_Forall
;         @u0
;         (Tm_refinement @x2 f)
;         (Tm_abs_25e3493e4b940364e027d68afed2c9f8 @u0 @x1 @x2 @x3 @x4))))
;     :qid l_quant_interp_6bba8ada8d83fbf9a31086f503e84f1b_alt))
;   :named l_quant_interp_6bba8ada8d83fbf9a31086f503e84f1b_alt)) 


(assert
 (! ;; def=FStar.Pervasives.fsti(265,46-265,72); use=FStar.Pervasives.fsti(265,46-265,72)
  (forall ((@u0 Universe) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (implies
        true
        (iff
          (Valid
            (Prims.l_Forall
            @u0
            (Tm_refinement @x2 (lambda ((x Term)) (Valid @x1)))
            (Tm_abs_25e3493e4b940364e027d68afed2c9f8 @u0 @x1 @x2 @x3 @x4)))
          (forall ((@x5 Term))
            (! (implies
              (and
              (HasType @x5 
                (Tm_refinement @x2 (lambda ((@x5 Term)) (Valid @x1)))
                )
              (Valid
                (ApplyTT @x3 @x5)))
              (Valid
              (ApplyTT @x4 @x5)))
            :qid l_quant_interp_6bba8ada8d83fbf9a31086f503e84f1b.1))))
    :pattern
     ((Valid
       (Prims.l_Forall
        @u0
        (Tm_refinement @x2 (lambda ((@x5 Term)) (Valid @x1)))
        (Tm_abs_25e3493e4b940364e027d68afed2c9f8 @u0 @x1 @x2 @x3 @x4))))
    :qid l_quant_interp_6bba8ada8d83fbf9a31086f503e84f1b))
  :named l_quant_interp_6bba8ada8d83fbf9a31086f503e84f1b))

(assert
 (! ;; def=FStar.Pervasives.fsti(265,39-265,72); use=FStar.Pervasives.fsti(265,39-265,72)
  (forall ((@x0 Term) (@u1 Universe) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (=
     (ApplyTT (Tm_abs_f4b968d76e465dbbe733c9606c5bd64d @u1 @x2 @x3 @x4) @x0)
     (Prims.l_and
      @x3
      (Prims.l_Forall
       @u1
       (Tm_refinement @x2 (lambda ((@x5 Term)) (Valid @x3)))
       (Tm_abs_25e3493e4b940364e027d68afed2c9f8 @u1 @x3 @x2 @x4 @x0))))
    :pattern ((ApplyTT (Tm_abs_f4b968d76e465dbbe733c9606c5bd64d @u1 @x2 @x3 @x4) @x0))
    :qid interpretation_Tm_abs_f4b968d76e465dbbe733c9606c5bd64d))
  :named interpretation_Tm_abs_f4b968d76e465dbbe733c9606c5bd64d))
(push) ;; push{0
(assert (! (= MaxFuel ZFuel) :named @MaxFuel_assumption))
(assert (! (= MaxIFuel ZFuel) :named @MaxIFuel_assumption))
(assert
 (! (not
   (forall ((@x0 Term) (@x1 Term) (@x2 Term))
    (! (implies
      (and
       (HasType @x0 (Tm_type uu___53))
       (HasType @x1 Prims.pure_pre)
       (HasType @x2 (Prims.pure_post_ uu___53 U_zero @x0 @x1)))
      (or
       label_1
       (Valid
        (Prims.pure_wp_monotonic0
         uu___53
         @x0
         (Tm_abs_f4b968d76e465dbbe733c9606c5bd64d uu___53 @x0 @x1 @x2)))))
     :qid @query)))
  :named @query))
(set-option :rlimit 2500000)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "<labels>")
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(get-unsat-core)
(pop) ;; 0}pop
