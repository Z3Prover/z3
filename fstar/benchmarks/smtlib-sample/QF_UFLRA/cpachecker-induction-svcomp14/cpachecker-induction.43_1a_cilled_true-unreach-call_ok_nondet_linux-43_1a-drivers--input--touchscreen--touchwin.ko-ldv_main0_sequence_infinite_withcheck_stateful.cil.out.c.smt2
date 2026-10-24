(set-info :smt-lib-version 2.6)
(set-logic QF_UFLRA)
(set-info :source |CPAchecker with k-induction on SV-COMP14 program using MathSAT5, submitted by Philipp Wendler, http://cpachecker.sosy-lab.org|)
(set-info :category "industrial")
(set-info :status unsat)


(declare-fun |main::ldv_s_tw_drv_serio_driver@1| () Real)
(declare-fun |tw_init::___cpa_temp_result_var_@1| () Real)
(declare-fun |tw_init::tmp@1| () Real)
(declare-fun ldv_spin@1 () Real)
(declare-fun |main::tmp@1| () Real)
(define-fun _7 () Real 0)
(define-fun _111 () Real 1)
(define-fun _1268 () Real |main::ldv_s_tw_drv_serio_driver@1|)
(define-fun _3054 () Real |tw_init::tmp@1|)
(define-fun _3055 () Bool (= _3054 _7))
(define-fun _3056 () Bool (<= _1268 _111))
(define-fun _3057 () Bool (<= _7 _1268))
(define-fun _3058 () Bool (and _3056 _3057))
(define-fun _3059 () Real |tw_init::___cpa_temp_result_var_@1|)
(define-fun _3060 () Bool (= _3059 _7))
(define-fun _3061 () Real |main::tmp@1|)
(define-fun _3062 () Bool (= _3061 _7))
(define-fun _3063 () Real ldv_spin@1)
(define-fun _3064 () Bool (= _3063 _7))
(define-fun _3065 () Bool (and _3062 _3064))
(define-fun _3066 () Bool (and _3060 _3065))
(define-fun _3067 () Bool (and _3058 _3066))
(define-fun _3068 () Bool (and _3055 _3067))
(define-fun _2 () Bool false)



(assert _3068)

(assert _2)
(check-sat)


(exit)
