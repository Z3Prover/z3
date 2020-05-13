; Copyright (c) 2017 Microsoft Corporation
; Github issue #...

(exit)
; theory seq seems to now diverge ungracefully
; z3str3 seems unsound

(set-option :produce-models true)
(set-info :smt-lib-version 2.5)
(set-option :smt.string_solver z3str3)
; regex = 0|(-?[1-9][0-9]*)
(define-fun ValidIntString ((s String)) Bool (str.in.re s (re.union (str.to.re "0") (re.++ (re.opt (str.to.re "-")) (re.range "1" "9") (re.* (re.range "0" "9"))))))
(define-fun IntToString ((i Int)) String (ite (< i 0) (str.++ "-" (int.to.str (- i))) (int.to.str i)))
(define-fun IntFromString ((s String)) Int (ite (= "-" (str.at s 0) )
                                                (- (str.to.int (str.replace s "-" ""))) 
                                                (str.to.int s) ))

(declare-fun int1() Int)
(declare-fun strInt1() String)
(assert (= int1 (IntFromString strInt1)))
(assert (ValidIntString strInt1))
(check-sat)
(get-value (int1 strInt1))

(declare-fun int2() Int)
(declare-fun strInt2() String)
(assert (= strInt2 (IntToString int2)))
(assert (ValidIntString strInt2))
(check-sat)
(get-value (int2 strInt2))