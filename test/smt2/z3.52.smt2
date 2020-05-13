
; Copyright (c) 2015 Microsoft Corporation
(set-option :auto-config true)
(set-option :produce-models true)

(set-option :smt.mbqi true)
(set-option :smt.macro-finder true)

(declare-sort Action)
(declare-sort Role)
(declare-sort Permission)
(declare-sort Id)

(declare-fun Client () Role)  
(declare-fun FinAdmin () Role)
(declare-fun FinClerk () Role)
(declare-fun Manager () Role)
(declare-fun POAdmin () Role)
(declare-fun POClerk () Role)
(declare-fun action2int (Action) Int)
(declare-fun id1 () Id)
(declare-fun id2 () Id)
(declare-fun id2int (Id) Int)
(declare-fun id3 () Id)
(declare-fun id4 () Id)
(declare-fun id5 () Id)
(declare-fun id6 () Id)
(declare-fun id7 () Id)
(declare-fun p1 () Permission)
(declare-fun p2 () Permission)
(declare-fun p3 () Permission)
(declare-fun p4 () Permission)
(declare-fun p5 () Permission)
(declare-fun p6 () Permission)
(declare-fun permission2int (Permission) Int)
(declare-fun role2int (Role) Int)
(declare-fun role_level (Role) Int)
(declare-fun t1_receive () Action)
(declare-fun t2_invoke () Action)
(declare-fun t3_split () Action)
(declare-fun t4_join () Action)
(declare-fun t5_invoke () Action)
(declare-fun t6_invoke () Action)
(declare-fun t7_invokeO () Action)
(declare-fun t8_invokeI () Action)
(declare-fun t9_invoke () Action)
(declare-fun in_creator_ctrPay_0 () Int)
(declare-fun in_creator_ctrPay_1 () Int)
(declare-fun in_customer_crtPO_0 () Int)
(declare-fun in_customer_crtPO_1 () Int)
(declare-fun out_approverPOPayment_apprPay_0 () Int)
(declare-fun out_approverPOPayment_apprPay_1 () Int)
(declare-fun out_approverPO_apprPO_0 () Int)
(declare-fun out_approverPO_apprPO_1 () Int)
(declare-fun out_creator_ctrPay_0 () Int)
(declare-fun out_creator_ctrPay_1 () Int)
(declare-fun out_signerGRN_ctrsignGRN_0 () Int)
(declare-fun out_signerGRN_ctrsignGRN_1 () Int)
(declare-fun out_signerGRN_signGRN_0 () Int)
(declare-fun out_signerGRN_signGRN_1 () Int)
(declare-fun p10_final_0 () Int)
(declare-fun p10_final_1 () Int)
(declare-fun p11_final_0 () Int)
(declare-fun p11_final_1 () Int)
(declare-fun p1_final_0 () Int)
(declare-fun p1_final_1 () Int)
(declare-fun p2_final_0 () Int)
(declare-fun p2_final_1 () Int)
(declare-fun p3_running_0 () Int)
(declare-fun p3_running_1 () Int)
(declare-fun p4_final_0 () Int)
(declare-fun p4_final_1 () Int)
(declare-fun p5_final_0 () Int)
(declare-fun p5_final_1 () Int)
(declare-fun p6_initial_0 () Int)
(declare-fun p6_initial_1 () Int)
(declare-fun p7_final_0 () Int)
(declare-fun p7_final_1 () Int)
(declare-fun p8_initial_0 () Int)
(declare-fun p8_initial_1 () Int)
(declare-fun p9_initial_0 () Int)
(declare-fun p9_initial_1 () Int)


;PREDICATES

(declare-fun has_permission (Id Action) Bool)
(declare-fun permission (Permission Action) Bool)
(declare-fun role (Role) Bool)
(declare-fun role_le (Role Role) Bool)
(declare-fun role_permission_assign (Role Permission) Bool)
(declare-fun user (Id) Bool)
(declare-fun user_role_assign (Id Role) Bool)
(declare-fun can_exec_0 (Id Action) Bool)
(declare-fun can_exec_1 (Id Action) Bool)
(declare-fun executed_0 (Id Action) Bool) 
(declare-fun executed_1 (Id Action) Bool)
(declare-fun initial_pm_0 () Bool)
(declare-fun initial_wf_0 () Bool)
(declare-fun t1_receive_0_1 (Id) Bool)
(declare-fun t2_invoke_0_1 (Id) Bool)
(declare-fun t3_split_0_1 (Id) Bool)
(declare-fun t4_join_0_1 (Id) Bool)
(declare-fun t5_invoke_0_1 (Id) Bool)
(declare-fun t6_invoke_0_1 (Id) Bool)
(declare-fun t7_invokeO_0_1 (Id) Bool)
(declare-fun t8_invokeI_0_1 (Id) Bool)
(declare-fun t9_invoke_0_1 (Id) Bool)

(assert
(forall ((?U Action) (?V Action)) (implies (= (action2int ?U) (action2int ?V)) (= ?U ?V))))
 

;assumption 2
(assert
(forall ((?U Action)) (and (<= 1 (action2int ?U)) (<= (action2int ?U) 9))))
 

;assumption 3
(assert
(= (action2int t1_receive) 1))

;assumption 4
(assert
(= (action2int t2_invoke) 2))

;assumption 5
(assert
(= (action2int t3_split) 3))

;assumption 6
(assert
(= (action2int t4_join) 4))

;assumption 7
(assert
(= (action2int t5_invoke) 5))

;assumption 8
(assert
(= (action2int t6_invoke) 6))

;assumption 9
(assert
(= (action2int t7_invokeO) 7))

;assumption 10
(assert
(= (action2int t8_invokeI) 8))

;assumption 11
(assert
(= (action2int t9_invoke) 9))

;assumption 12
(assert
(forall ((?U Role) (?V Role)) (implies (= (role2int ?U) (role2int ?V)) (= ?U ?V))))
 

;assumption 13
(assert
(forall ((?U Role)) (and (<= 1 (role2int ?U)) (<= (role2int ?U) 6))))
 

;assumption 14
(assert
(= (role2int Manager) 1))

;assumption 15
(assert
(= (role2int FinAdmin) 2))

;assumption 16
(assert
(= (role2int FinClerk) 3))

;assumption 17
(assert
(= (role2int POAdmin) 4))

;assumption 18
(assert
(= (role2int POClerk) 5))

;assumption 19
(assert
(= (role2int Client) 6))

;assumption 20
(assert
(forall ((?U Permission) (?V Permission)) (implies (= (permission2int ?U) (permission2int ?V)) (= ?U ?V))))
 

;assumption 21
(assert
(forall ((?U Permission)) (and (<= 1 (permission2int ?U)) (<= (permission2int ?U) 6))))
 

;assumption 22
(assert
(= (permission2int p1) 1))

;assumption 23
(assert
(= (permission2int p2) 2))

;assumption 24
(assert
(= (permission2int p3) 3))

;assumption 25
(assert
(= (permission2int p4) 4))

;assumption 26
(assert
(= (permission2int p5) 5))

;assumption 27
(assert
(= (permission2int p6) 6))

;assumption 28
(assert
(forall ((?U Permission) (?V Action)) (iff (permission ?U ?V) (or (and (= ?U p1) (= ?V t2_invoke)) (or (and (= ?U p2) (= ?V t5_invoke)) (or (and (= ?U p3) (= ?V t6_invoke)) (or (and (= ?U p4) (or (= ?V t7_invokeO) (= ?V t8_invokeI))) (or (and (= ?U p5) (= ?V t9_invoke)) (and (= ?U p6) (= ?V t1_receive))))))))))
 

;assumption 29
(assert
(forall ((?U Id) (?V Role)) (iff (user_role_assign ?U ?V) (or (and (= ?U id7) (= ?V Manager)) (or (and (= ?U id1) (= ?V Manager)) (or (and (= ?U id2) (= ?V FinAdmin)) (or (and (= ?U id3) (= ?V FinClerk)) (or (and (= ?U id4) (= ?V POAdmin)) (or (and (= ?U id5) (= ?V POClerk)) (and (= ?U id6) (= ?V Client)))))))))))
 

;assumption 30
(assert
(forall ((?U Role) (?V Permission)) (iff (role_permission_assign ?U ?V) (or (and (= ?U POClerk) (= ?V p3)) (or (and (= ?U FinClerk) (= ?V p4)) (or (and (= ?U POAdmin) (or (= ?V p1) (= ?V p3))) (or (and (= ?U FinAdmin) (or (= ?V p5) (= ?V p4))) (or (and (= ?U Client) (or (= ?V p6) (= ?V p2))) (and (= ?U Manager) (or (= ?V p1) (or (= ?V p3) (or (= ?V p4) (= ?V p5)))))))))))))
 

;assumption 31
(assert
(forall ((?U Id) (?V Action)) (iff (has_permission ?U ?V) (or (and (user_role_assign ?U Manager) (and (role_permission_assign Manager p1) (permission p1 ?V))) (or (and (user_role_assign ?U Manager) (and (role_permission_assign Manager p2) (permission p2 ?V))) (or (and (user_role_assign ?U Manager) (and (role_permission_assign Manager p3) (permission p3 ?V))) (or (and (user_role_assign ?U Manager) (and (role_permission_assign Manager p4) (permission p4 ?V))) (or (and (user_role_assign ?U Manager) (and (role_permission_assign Manager p5) (permission p5 ?V))) (or (and (user_role_assign ?U Manager) (and (role_permission_assign Manager p6) (permission p6 ?V))) (or (and (user_role_assign ?U POClerk) (and (role_permission_assign POClerk p1) (permission p1 ?V))) (or (and (user_role_assign ?U POClerk) (and (role_permission_assign POClerk p2) (permission p2 ?V))) (or (and (user_role_assign ?U POClerk) (and (role_permission_assign POClerk p3) (permission p3 ?V))) (or (and (user_role_assign ?U POClerk) (and (role_permission_assign POClerk p4) (permission p4 ?V))) (or (and (user_role_assign ?U POClerk) (and (role_permission_assign POClerk p5) (permission p5 ?V))) (or (and (user_role_assign ?U POClerk) (and (role_permission_assign POClerk p6) (permission p6 ?V))) (or (and (user_role_assign ?U FinClerk) (and (role_permission_assign FinClerk p1) (permission p1 ?V))) (or (and (user_role_assign ?U FinClerk) (and (role_permission_assign FinClerk p2) (permission p2 ?V))) (or (and (user_role_assign ?U FinClerk) (and (role_permission_assign FinClerk p3) (permission p3 ?V))) (or (and (user_role_assign ?U FinClerk) (and (role_permission_assign FinClerk p4) (permission p4 ?V))) (or (and (user_role_assign ?U FinClerk) (and (role_permission_assign FinClerk p5) (permission p5 ?V))) (or (and (user_role_assign ?U FinClerk) (and (role_permission_assign FinClerk p6) (permission p6 ?V))) (or (and (user_role_assign ?U FinAdmin) (and (role_permission_assign FinAdmin p1) (permission p1 ?V))) (or (and (user_role_assign ?U FinAdmin) (and (role_permission_assign FinAdmin p2) (permission p2 ?V))) (or (and (user_role_assign ?U FinAdmin) (and (role_permission_assign FinAdmin p3) (permission p3 ?V))) (or (and (user_role_assign ?U FinAdmin) (and (role_permission_assign FinAdmin p4) (permission p4 ?V))) (or (and (user_role_assign ?U FinAdmin) (and (role_permission_assign FinAdmin p5) (permission p5 ?V))) (or (and (user_role_assign ?U FinAdmin) (and (role_permission_assign FinAdmin p6) (permission p6 ?V))) (or (and (user_role_assign ?U POAdmin) (and (role_permission_assign POAdmin p1) (permission p1 ?V))) (or (and (user_role_assign ?U POAdmin) (and (role_permission_assign POAdmin p2) (permission p2 ?V))) (or (and (user_role_assign ?U POAdmin) (and (role_permission_assign POAdmin p3) (permission p3 ?V))) (or (and (user_role_assign ?U POAdmin) (and (role_permission_assign POAdmin p4) (permission p4 ?V))) (or (and (user_role_assign ?U POAdmin) (and (role_permission_assign POAdmin p5) (permission p5 ?V))) (or (and (user_role_assign ?U POAdmin) (and (role_permission_assign POAdmin p6) (permission p6 ?V))) (or (and (user_role_assign ?U Client) (and (role_permission_assign Client p1) (permission p1 ?V))) (or (and (user_role_assign ?U Client) (and (role_permission_assign Client p2) (permission p2 ?V))) (or (and (user_role_assign ?U Client) (and (role_permission_assign Client p3) (permission p3 ?V))) (or (and (user_role_assign ?U Client) (and (role_permission_assign Client p4) (permission p4 ?V))) (or (and (user_role_assign ?U Client) (and (role_permission_assign Client p5) (permission p5 ?V))) (and (user_role_assign ?U Client) (and (role_permission_assign Client p6) (permission p6 ?V)))))))))))))))))))))))))))))))))))))))))
 

;assumption 32
(assert
(forall ((?U Role) (?V Role)) (iff (role_le ?U ?V) (< (role_level ?U) (role_level ?V)))))
 

;assumption 33
(assert
(= (role_level Manager) 3))

;assumption 34
(assert
(= (role_level FinAdmin) 2))

;assumption 35
(assert
(= (role_level FinClerk) 1))

;assumption 36
(assert
(= (role_level POAdmin) 2))

;assumption 37
(assert
(= (role_level POClerk) 1))

;assumption 38
(assert
(= (role_level Client) 0))

;assumption 39
(assert
(forall ((?U Id) (?V Id)) (implies (= (id2int ?U) (id2int ?V)) (= ?U ?V))))
 

;assumption 40
(assert
(forall ((?U Id)) (and (<= 1 (id2int ?U)) (<= (id2int ?U) 7))))
 

;assumption 41
(assert
(= (id2int id1) 1))

;assumption 42
(assert
(= (id2int id2) 2))

;assumption 43
(assert
(= (id2int id3) 3))

;assumption 44
(assert
(= (id2int id4) 4))

;assumption 45
(assert
(= (id2int id5) 5))

;assumption 46
(assert
(= (id2int id6) 6))

;assumption 47
(assert
(= (id2int id7) 7))

;assumption 48
(assert
(iff initial_wf_0 (and (= p1_final_0 0) (and (= p2_final_0 0) (and (= p3_running_0 0) (and (= p4_final_0 0) (and (= p5_final_0 0) (and (= p6_initial_0 0) (and (= p7_final_0 0) (and (= p8_initial_0 0) (and (= p9_initial_0 1) (and (= p10_final_0 0) (and (= p11_final_0 0) (and (= in_customer_crtPO_0 1) (and (= in_creator_ctrPay_0 1) (and (= out_approverPO_apprPO_0 0) (and (= out_approverPOPayment_apprPay_0 0) (and (= out_creator_ctrPay_0 0) (and (= out_signerGRN_ctrsignGRN_0 0) (= out_signerGRN_signGRN_0 0))))))))))))))))))))

;assumption 49
(assert
(iff initial_pm_0 (forall ((?U Id) (?V Action)) (iff (executed_0 ?U ?V) false))
 ))

;assumption 50
(assert
(forall ((?U Id) (?V Action)) (iff (can_exec_0 ?U ?V) (or (and (= ?V t5_invoke) (and (has_permission ?U t5_invoke) (or (and (not (= ?U id1)) (executed_0 id1 t2_invoke)) (or (and (not (= ?U id2)) (executed_0 id2 t2_invoke)) (or (and (not (= ?U id3)) (executed_0 id3 t2_invoke)) (or (and (not (= ?U id4)) (executed_0 id4 t2_invoke)) (or (and (not (= ?U id5)) (executed_0 id5 t2_invoke)) (or (and (not (= ?U id6)) (executed_0 id6 t2_invoke)) (and (not (= ?U id7)) (executed_0 id7 t2_invoke)))))))))) (or (and (= ?V t6_invoke) (and (and (has_permission ?U t6_invoke) (or (and (not (= ?U id1)) (executed_0 id1 t2_invoke)) (or (and (not (= ?U id2)) (executed_0 id2 t2_invoke)) (or (and (not (= ?U id3)) (executed_0 id3 t2_invoke)) (or (and (not (= ?U id4)) (executed_0 id4 t2_invoke)) (or (and (not (= ?U id5)) (executed_0 id5 t2_invoke)) (or (and (not (= ?U id6)) (executed_0 id6 t2_invoke)) (and (not (= ?U id7)) (executed_0 id7 t2_invoke))))))))) (and (has_permission ?U t6_invoke) (or (and (not (= ?U id1)) (executed_0 id1 t5_invoke)) (or (and (not (= ?U id2)) (executed_0 id2 t5_invoke)) (or (and (not (= ?U id3)) (executed_0 id3 t5_invoke)) (or (and (not (= ?U id4)) (executed_0 id4 t5_invoke)) (or (and (not (= ?U id5)) (executed_0 id5 t5_invoke)) (or (and (not (= ?U id6)) (executed_0 id6 t5_invoke)) (and (not (= ?U id7)) (executed_0 id7 t5_invoke))))))))))) (or (and (= ?V t9_invoke) (and (has_permission ?U t9_invoke) (exists ((?W Role))  (and (user_role_assign ?U ?W) (and (or (and (user_role_assign id1 Manager) (and (role_le Manager ?W) (executed_0 id1 t7_invokeO))) (or (and (user_role_assign id2 Manager) (and (role_le Manager ?W) (executed_0 id2 t7_invokeO))) (or (and (user_role_assign id3 Manager) (and (role_le Manager ?W) (executed_0 id3 t7_invokeO))) (or (and (user_role_assign id4 Manager) (and (role_le Manager ?W) (executed_0 id4 t7_invokeO))) (or (and (user_role_assign id5 Manager) (and (role_le Manager ?W) (executed_0 id5 t7_invokeO))) (or (and (user_role_assign id6 Manager) (and (role_le Manager ?W) (executed_0 id6 t7_invokeO))) (or (and (user_role_assign id7 Manager) (and (role_le Manager ?W) (executed_0 id7 t7_invokeO))) (or (and (user_role_assign id1 POClerk) (and (role_le POClerk ?W) (executed_0 id1 t7_invokeO))) (or (and (user_role_assign id2 POClerk) (and (role_le POClerk ?W) (executed_0 id2 t7_invokeO))) (or (and (user_role_assign id3 POClerk) (and (role_le POClerk ?W) (executed_0 id3 t7_invokeO))) (or (and (user_role_assign id4 POClerk) (and (role_le POClerk ?W) (executed_0 id4 t7_invokeO))) (or (and (user_role_assign id5 POClerk) (and (role_le POClerk ?W) (executed_0 id5 t7_invokeO))) (or (and (user_role_assign id6 POClerk) (and (role_le POClerk ?W) (executed_0 id6 t7_invokeO))) (or (and (user_role_assign id7 POClerk) (and (role_le POClerk ?W) (executed_0 id7 t7_invokeO))) (or (and (user_role_assign id1 FinClerk) (and (role_le FinClerk ?W) (executed_0 id1 t7_invokeO))) (or (and (user_role_assign id2 FinClerk) (and (role_le FinClerk ?W) (executed_0 id2 t7_invokeO))) (or (and (user_role_assign id3 FinClerk) (and (role_le FinClerk ?W) (executed_0 id3 t7_invokeO))) (or (and (user_role_assign id4 FinClerk) (and (role_le FinClerk ?W) (executed_0 id4 t7_invokeO))) (or (and (user_role_assign id5 FinClerk) (and (role_le FinClerk ?W) (executed_0 id5 t7_invokeO))) (or (and (user_role_assign id6 FinClerk) (and (role_le FinClerk ?W) (executed_0 id6 t7_invokeO))) (or (and (user_role_assign id7 FinClerk) (and (role_le FinClerk ?W) (executed_0 id7 t7_invokeO))) (or (and (user_role_assign id1 FinAdmin) (and (role_le FinAdmin ?W) (executed_0 id1 t7_invokeO))) (or (and (user_role_assign id2 FinAdmin) (and (role_le FinAdmin ?W) (executed_0 id2 t7_invokeO))) (or (and (user_role_assign id3 FinAdmin) (and (role_le FinAdmin ?W) (executed_0 id3 t7_invokeO))) (or (and (user_role_assign id4 FinAdmin) (and (role_le FinAdmin ?W) (executed_0 id4 t7_invokeO))) (or (and (user_role_assign id5 FinAdmin) (and (role_le FinAdmin ?W) (executed_0 id5 t7_invokeO))) (or (and (user_role_assign id6 FinAdmin) (and (role_le FinAdmin ?W) (executed_0 id6 t7_invokeO))) (or (and (user_role_assign id7 FinAdmin) (and (role_le FinAdmin ?W) (executed_0 id7 t7_invokeO))) (or (and (user_role_assign id1 POAdmin) (and (role_le POAdmin ?W) (executed_0 id1 t7_invokeO))) (or (and (user_role_assign id2 POAdmin) (and (role_le POAdmin ?W) (executed_0 id2 t7_invokeO))) (or (and (user_role_assign id3 POAdmin) (and (role_le POAdmin ?W) (executed_0 id3 t7_invokeO))) (or (and (user_role_assign id4 POAdmin) (and (role_le POAdmin ?W) (executed_0 id4 t7_invokeO))) (or (and (user_role_assign id5 POAdmin) (and (role_le POAdmin ?W) (executed_0 id5 t7_invokeO))) (or (and (user_role_assign id6 POAdmin) (and (role_le POAdmin ?W) (executed_0 id6 t7_invokeO))) (or (and (user_role_assign id7 POAdmin) (and (role_le POAdmin ?W) (executed_0 id7 t7_invokeO))) (or (and (user_role_assign id1 Client) (and (role_le Client ?W) (executed_0 id1 t7_invokeO))) (or (and (user_role_assign id2 Client) (and (role_le Client ?W) (executed_0 id2 t7_invokeO))) (or (and (user_role_assign id3 Client) (and (role_le Client ?W) (executed_0 id3 t7_invokeO))) (or (and (user_role_assign id4 Client) (and (role_le Client ?W) (executed_0 id4 t7_invokeO))) (or (and (user_role_assign id5 Client) (and (role_le Client ?W) (executed_0 id5 t7_invokeO))) (or (and (user_role_assign id6 Client) (and (role_le Client ?W) (executed_0 id6 t7_invokeO))) (and (user_role_assign id7 Client) (and (role_le Client ?W) (executed_0 id7 t7_invokeO)))))))))))))))))))))))))))))))))))))))))))) (or (and (user_role_assign id1 Manager) (and (role_le Manager ?W) (executed_0 id1 t8_invokeI))) (or (and (user_role_assign id2 Manager) (and (role_le Manager ?W) (executed_0 id2 t8_invokeI))) (or (and (user_role_assign id3 Manager) (and (role_le Manager ?W) (executed_0 id3 t8_invokeI))) (or (and (user_role_assign id4 Manager) (and (role_le Manager ?W) (executed_0 id4 t8_invokeI))) (or (and (user_role_assign id5 Manager) (and (role_le Manager ?W) (executed_0 id5 t8_invokeI))) (or (and (user_role_assign id6 Manager) (and (role_le Manager ?W) (executed_0 id6 t8_invokeI))) (or (and (user_role_assign id7 Manager) (and (role_le Manager ?W) (executed_0 id7 t8_invokeI))) (or (and (user_role_assign id1 POClerk) (and (role_le POClerk ?W) (executed_0 id1 t8_invokeI))) (or (and (user_role_assign id2 POClerk) (and (role_le POClerk ?W) (executed_0 id2 t8_invokeI))) (or (and (user_role_assign id3 POClerk) (and (role_le POClerk ?W) (executed_0 id3 t8_invokeI))) (or (and (user_role_assign id4 POClerk) (and (role_le POClerk ?W) (executed_0 id4 t8_invokeI))) (or (and (user_role_assign id5 POClerk) (and (role_le POClerk ?W) (executed_0 id5 t8_invokeI))) (or (and (user_role_assign id6 POClerk) (and (role_le POClerk ?W) (executed_0 id6 t8_invokeI))) (or (and (user_role_assign id7 POClerk) (and (role_le POClerk ?W) (executed_0 id7 t8_invokeI))) (or (and (user_role_assign id1 FinClerk) (and (role_le FinClerk ?W) (executed_0 id1 t8_invokeI))) (or (and (user_role_assign id2 FinClerk) (and (role_le FinClerk ?W) (executed_0 id2 t8_invokeI))) (or (and (user_role_assign id3 FinClerk) (and (role_le FinClerk ?W) (executed_0 id3 t8_invokeI))) (or (and (user_role_assign id4 FinClerk) (and (role_le FinClerk ?W) (executed_0 id4 t8_invokeI))) (or (and (user_role_assign id5 FinClerk) (and (role_le FinClerk ?W) (executed_0 id5 t8_invokeI))) (or (and (user_role_assign id6 FinClerk) (and (role_le FinClerk ?W) (executed_0 id6 t8_invokeI))) (or (and (user_role_assign id7 FinClerk) (and (role_le FinClerk ?W) (executed_0 id7 t8_invokeI))) (or (and (user_role_assign id1 FinAdmin) (and (role_le FinAdmin ?W) (executed_0 id1 t8_invokeI))) (or (and (user_role_assign id2 FinAdmin) (and (role_le FinAdmin ?W) (executed_0 id2 t8_invokeI))) (or (and (user_role_assign id3 FinAdmin) (and (role_le FinAdmin ?W) (executed_0 id3 t8_invokeI))) (or (and (user_role_assign id4 FinAdmin) (and (role_le FinAdmin ?W) (executed_0 id4 t8_invokeI))) (or (and (user_role_assign id5 FinAdmin) (and (role_le FinAdmin ?W) (executed_0 id5 t8_invokeI))) (or (and (user_role_assign id6 FinAdmin) (and (role_le FinAdmin ?W) (executed_0 id6 t8_invokeI))) (or (and (user_role_assign id7 FinAdmin) (and (role_le FinAdmin ?W) (executed_0 id7 t8_invokeI))) (or (and (user_role_assign id1 POAdmin) (and (role_le POAdmin ?W) (executed_0 id1 t8_invokeI))) (or (and (user_role_assign id2 POAdmin) (and (role_le POAdmin ?W) (executed_0 id2 t8_invokeI))) (or (and (user_role_assign id3 POAdmin) (and (role_le POAdmin ?W) (executed_0 id3 t8_invokeI))) (or (and (user_role_assign id4 POAdmin) (and (role_le POAdmin ?W) (executed_0 id4 t8_invokeI))) (or (and (user_role_assign id5 POAdmin) (and (role_le POAdmin ?W) (executed_0 id5 t8_invokeI))) (or (and (user_role_assign id6 POAdmin) (and (role_le POAdmin ?W) (executed_0 id6 t8_invokeI))) (or (and (user_role_assign id7 POAdmin) (and (role_le POAdmin ?W) (executed_0 id7 t8_invokeI))) (or (and (user_role_assign id1 Client) (and (role_le Client ?W) (executed_0 id1 t8_invokeI))) (or (and (user_role_assign id2 Client) (and (role_le Client ?W) (executed_0 id2 t8_invokeI))) (or (and (user_role_assign id3 Client) (and (role_le Client ?W) (executed_0 id3 t8_invokeI))) (or (and (user_role_assign id4 Client) (and (role_le Client ?W) (executed_0 id4 t8_invokeI))) (or (and (user_role_assign id5 Client) (and (role_le Client ?W) (executed_0 id5 t8_invokeI))) (or (and (user_role_assign id6 Client) (and (role_le Client ?W) (executed_0 id6 t8_invokeI))) (and (user_role_assign id7 Client) (and (role_le Client ?W) (executed_0 id7 t8_invokeI))))))))))))))))))))))))))))))))))))))))))))) )) )) (or (and (= ?V t1_receive) (has_permission ?U t1_receive)) (or (and (= ?V t2_invoke) (has_permission ?U t2_invoke)) (or (and (= ?V t7_invokeO) (has_permission ?U t7_invokeO)) (and (= ?V t8_invokeI) (has_permission ?U t8_invokeI)))))))))))
 

;assumption 51
(assert
(forall ((?U Id) (?V Action)) (iff (can_exec_1 ?U ?V) (or (and (= ?V t5_invoke) (and (has_permission ?U t5_invoke) (or (and (not (= ?U id1)) (executed_1 id1 t2_invoke)) (or (and (not (= ?U id2)) (executed_1 id2 t2_invoke)) (or (and (not (= ?U id3)) (executed_1 id3 t2_invoke)) (or (and (not (= ?U id4)) (executed_1 id4 t2_invoke)) (or (and (not (= ?U id5)) (executed_1 id5 t2_invoke)) (or (and (not (= ?U id6)) (executed_1 id6 t2_invoke)) (and (not (= ?U id7)) (executed_1 id7 t2_invoke)))))))))) (or (and (= ?V t6_invoke) (and (and (has_permission ?U t6_invoke) (or (and (not (= ?U id1)) (executed_1 id1 t2_invoke)) (or (and (not (= ?U id2)) (executed_1 id2 t2_invoke)) (or (and (not (= ?U id3)) (executed_1 id3 t2_invoke)) (or (and (not (= ?U id4)) (executed_1 id4 t2_invoke)) (or (and (not (= ?U id5)) (executed_1 id5 t2_invoke)) (or (and (not (= ?U id6)) (executed_1 id6 t2_invoke)) (and (not (= ?U id7)) (executed_1 id7 t2_invoke))))))))) (and (has_permission ?U t6_invoke) (or (and (not (= ?U id1)) (executed_1 id1 t5_invoke)) (or (and (not (= ?U id2)) (executed_1 id2 t5_invoke)) (or (and (not (= ?U id3)) (executed_1 id3 t5_invoke)) (or (and (not (= ?U id4)) (executed_1 id4 t5_invoke)) (or (and (not (= ?U id5)) (executed_1 id5 t5_invoke)) (or (and (not (= ?U id6)) (executed_1 id6 t5_invoke)) (and (not (= ?U id7)) (executed_1 id7 t5_invoke))))))))))) (or (and (= ?V t9_invoke) (and (has_permission ?U t9_invoke) (exists ((?W Role))  (and (user_role_assign ?U ?W) (and (or (and (user_role_assign id1 Manager) (and (role_le Manager ?W) (executed_1 id1 t7_invokeO))) (or (and (user_role_assign id2 Manager) (and (role_le Manager ?W) (executed_1 id2 t7_invokeO))) (or (and (user_role_assign id3 Manager) (and (role_le Manager ?W) (executed_1 id3 t7_invokeO))) (or (and (user_role_assign id4 Manager) (and (role_le Manager ?W) (executed_1 id4 t7_invokeO))) (or (and (user_role_assign id5 Manager) (and (role_le Manager ?W) (executed_1 id5 t7_invokeO))) (or (and (user_role_assign id6 Manager) (and (role_le Manager ?W) (executed_1 id6 t7_invokeO))) (or (and (user_role_assign id7 Manager) (and (role_le Manager ?W) (executed_1 id7 t7_invokeO))) (or (and (user_role_assign id1 POClerk) (and (role_le POClerk ?W) (executed_1 id1 t7_invokeO))) (or (and (user_role_assign id2 POClerk) (and (role_le POClerk ?W) (executed_1 id2 t7_invokeO))) (or (and (user_role_assign id3 POClerk) (and (role_le POClerk ?W) (executed_1 id3 t7_invokeO))) (or (and (user_role_assign id4 POClerk) (and (role_le POClerk ?W) (executed_1 id4 t7_invokeO))) (or (and (user_role_assign id5 POClerk) (and (role_le POClerk ?W) (executed_1 id5 t7_invokeO))) (or (and (user_role_assign id6 POClerk) (and (role_le POClerk ?W) (executed_1 id6 t7_invokeO))) (or (and (user_role_assign id7 POClerk) (and (role_le POClerk ?W) (executed_1 id7 t7_invokeO))) (or (and (user_role_assign id1 FinClerk) (and (role_le FinClerk ?W) (executed_1 id1 t7_invokeO))) (or (and (user_role_assign id2 FinClerk) (and (role_le FinClerk ?W) (executed_1 id2 t7_invokeO))) (or (and (user_role_assign id3 FinClerk) (and (role_le FinClerk ?W) (executed_1 id3 t7_invokeO))) (or (and (user_role_assign id4 FinClerk) (and (role_le FinClerk ?W) (executed_1 id4 t7_invokeO))) (or (and (user_role_assign id5 FinClerk) (and (role_le FinClerk ?W) (executed_1 id5 t7_invokeO))) (or (and (user_role_assign id6 FinClerk) (and (role_le FinClerk ?W) (executed_1 id6 t7_invokeO))) (or (and (user_role_assign id7 FinClerk) (and (role_le FinClerk ?W) (executed_1 id7 t7_invokeO))) (or (and (user_role_assign id1 FinAdmin) (and (role_le FinAdmin ?W) (executed_1 id1 t7_invokeO))) (or (and (user_role_assign id2 FinAdmin) (and (role_le FinAdmin ?W) (executed_1 id2 t7_invokeO))) (or (and (user_role_assign id3 FinAdmin) (and (role_le FinAdmin ?W) (executed_1 id3 t7_invokeO))) (or (and (user_role_assign id4 FinAdmin) (and (role_le FinAdmin ?W) (executed_1 id4 t7_invokeO))) (or (and (user_role_assign id5 FinAdmin) (and (role_le FinAdmin ?W) (executed_1 id5 t7_invokeO))) (or (and (user_role_assign id6 FinAdmin) (and (role_le FinAdmin ?W) (executed_1 id6 t7_invokeO))) (or (and (user_role_assign id7 FinAdmin) (and (role_le FinAdmin ?W) (executed_1 id7 t7_invokeO))) (or (and (user_role_assign id1 POAdmin) (and (role_le POAdmin ?W) (executed_1 id1 t7_invokeO))) (or (and (user_role_assign id2 POAdmin) (and (role_le POAdmin ?W) (executed_1 id2 t7_invokeO))) (or (and (user_role_assign id3 POAdmin) (and (role_le POAdmin ?W) (executed_1 id3 t7_invokeO))) (or (and (user_role_assign id4 POAdmin) (and (role_le POAdmin ?W) (executed_1 id4 t7_invokeO))) (or (and (user_role_assign id5 POAdmin) (and (role_le POAdmin ?W) (executed_1 id5 t7_invokeO))) (or (and (user_role_assign id6 POAdmin) (and (role_le POAdmin ?W) (executed_1 id6 t7_invokeO))) (or (and (user_role_assign id7 POAdmin) (and (role_le POAdmin ?W) (executed_1 id7 t7_invokeO))) (or (and (user_role_assign id1 Client) (and (role_le Client ?W) (executed_1 id1 t7_invokeO))) (or (and (user_role_assign id2 Client) (and (role_le Client ?W) (executed_1 id2 t7_invokeO))) (or (and (user_role_assign id3 Client) (and (role_le Client ?W) (executed_1 id3 t7_invokeO))) (or (and (user_role_assign id4 Client) (and (role_le Client ?W) (executed_1 id4 t7_invokeO))) (or (and (user_role_assign id5 Client) (and (role_le Client ?W) (executed_1 id5 t7_invokeO))) (or (and (user_role_assign id6 Client) (and (role_le Client ?W) (executed_1 id6 t7_invokeO))) (and (user_role_assign id7 Client) (and (role_le Client ?W) (executed_1 id7 t7_invokeO)))))))))))))))))))))))))))))))))))))))))))) (or (and (user_role_assign id1 Manager) (and (role_le Manager ?W) (executed_1 id1 t8_invokeI))) (or (and (user_role_assign id2 Manager) (and (role_le Manager ?W) (executed_1 id2 t8_invokeI))) (or (and (user_role_assign id3 Manager) (and (role_le Manager ?W) (executed_1 id3 t8_invokeI))) (or (and (user_role_assign id4 Manager) (and (role_le Manager ?W) (executed_1 id4 t8_invokeI))) (or (and (user_role_assign id5 Manager) (and (role_le Manager ?W) (executed_1 id5 t8_invokeI))) (or (and (user_role_assign id6 Manager) (and (role_le Manager ?W) (executed_1 id6 t8_invokeI))) (or (and (user_role_assign id7 Manager) (and (role_le Manager ?W) (executed_1 id7 t8_invokeI))) (or (and (user_role_assign id1 POClerk) (and (role_le POClerk ?W) (executed_1 id1 t8_invokeI))) (or (and (user_role_assign id2 POClerk) (and (role_le POClerk ?W) (executed_1 id2 t8_invokeI))) (or (and (user_role_assign id3 POClerk) (and (role_le POClerk ?W) (executed_1 id3 t8_invokeI))) (or (and (user_role_assign id4 POClerk) (and (role_le POClerk ?W) (executed_1 id4 t8_invokeI))) (or (and (user_role_assign id5 POClerk) (and (role_le POClerk ?W) (executed_1 id5 t8_invokeI))) (or (and (user_role_assign id6 POClerk) (and (role_le POClerk ?W) (executed_1 id6 t8_invokeI))) (or (and (user_role_assign id7 POClerk) (and (role_le POClerk ?W) (executed_1 id7 t8_invokeI))) (or (and (user_role_assign id1 FinClerk) (and (role_le FinClerk ?W) (executed_1 id1 t8_invokeI))) (or (and (user_role_assign id2 FinClerk) (and (role_le FinClerk ?W) (executed_1 id2 t8_invokeI))) (or (and (user_role_assign id3 FinClerk) (and (role_le FinClerk ?W) (executed_1 id3 t8_invokeI))) (or (and (user_role_assign id4 FinClerk) (and (role_le FinClerk ?W) (executed_1 id4 t8_invokeI))) (or (and (user_role_assign id5 FinClerk) (and (role_le FinClerk ?W) (executed_1 id5 t8_invokeI))) (or (and (user_role_assign id6 FinClerk) (and (role_le FinClerk ?W) (executed_1 id6 t8_invokeI))) (or (and (user_role_assign id7 FinClerk) (and (role_le FinClerk ?W) (executed_1 id7 t8_invokeI))) (or (and (user_role_assign id1 FinAdmin) (and (role_le FinAdmin ?W) (executed_1 id1 t8_invokeI))) (or (and (user_role_assign id2 FinAdmin) (and (role_le FinAdmin ?W) (executed_1 id2 t8_invokeI))) (or (and (user_role_assign id3 FinAdmin) (and (role_le FinAdmin ?W) (executed_1 id3 t8_invokeI))) (or (and (user_role_assign id4 FinAdmin) (and (role_le FinAdmin ?W) (executed_1 id4 t8_invokeI))) (or (and (user_role_assign id5 FinAdmin) (and (role_le FinAdmin ?W) (executed_1 id5 t8_invokeI))) (or (and (user_role_assign id6 FinAdmin) (and (role_le FinAdmin ?W) (executed_1 id6 t8_invokeI))) (or (and (user_role_assign id7 FinAdmin) (and (role_le FinAdmin ?W) (executed_1 id7 t8_invokeI))) (or (and (user_role_assign id1 POAdmin) (and (role_le POAdmin ?W) (executed_1 id1 t8_invokeI))) (or (and (user_role_assign id2 POAdmin) (and (role_le POAdmin ?W) (executed_1 id2 t8_invokeI))) (or (and (user_role_assign id3 POAdmin) (and (role_le POAdmin ?W) (executed_1 id3 t8_invokeI))) (or (and (user_role_assign id4 POAdmin) (and (role_le POAdmin ?W) (executed_1 id4 t8_invokeI))) (or (and (user_role_assign id5 POAdmin) (and (role_le POAdmin ?W) (executed_1 id5 t8_invokeI))) (or (and (user_role_assign id6 POAdmin) (and (role_le POAdmin ?W) (executed_1 id6 t8_invokeI))) (or (and (user_role_assign id7 POAdmin) (and (role_le POAdmin ?W) (executed_1 id7 t8_invokeI))) (or (and (user_role_assign id1 Client) (and (role_le Client ?W) (executed_1 id1 t8_invokeI))) (or (and (user_role_assign id2 Client) (and (role_le Client ?W) (executed_1 id2 t8_invokeI))) (or (and (user_role_assign id3 Client) (and (role_le Client ?W) (executed_1 id3 t8_invokeI))) (or (and (user_role_assign id4 Client) (and (role_le Client ?W) (executed_1 id4 t8_invokeI))) (or (and (user_role_assign id5 Client) (and (role_le Client ?W) (executed_1 id5 t8_invokeI))) (or (and (user_role_assign id6 Client) (and (role_le Client ?W) (executed_1 id6 t8_invokeI))) (and (user_role_assign id7 Client) (and (role_le Client ?W) (executed_1 id7 t8_invokeI))))))))))))))))))))))))))))))))))))))))))))) )) )) (or (and (= ?V t1_receive) (has_permission ?U t1_receive)) (or (and (= ?V t2_invoke) (has_permission ?U t2_invoke)) (or (and (= ?V t7_invokeO) (has_permission ?U t7_invokeO)) (and (= ?V t8_invokeI) (has_permission ?U t8_invokeI)))))))))))
 

;assumption 52
(assert
(forall ((?U Id)) (iff (t1_receive_0_1 ?U)
   (and (and (can_exec_0 ?U t1_receive) (and (<= 1 in_customer_crtPO_0) (<= 1 p9_initial_0)))
  (and (and (= p1_final_1 p1_final_0) (and (= p2_final_1 p2_final_0) (and (= p3_running_1 p3_running_0) (and (= p4_final_1 p4_final_0) (and (= p5_final_1 p5_final_0) (and (= p6_initial_1 p6_initial_0) (and (= p7_final_1 p7_final_0) (and (= p8_initial_1 p8_initial_0) (and (= p9_initial_1 (+ (~ 1) p9_initial_0)) (and (= p10_final_1 (+ 1 p10_final_0)) (and (= p11_final_1 p11_final_0) (and (= in_customer_crtPO_1 (+ (~ 1) in_customer_crtPO_0)) (and (= in_creator_ctrPay_1 in_creator_ctrPay_0) (and (= out_creator_ctrPay_1 out_creator_ctrPay_0) (and (= out_approverPOPayment_apprPay_1 out_approverPOPayment_apprPay_0) (and (= out_approverPO_apprPO_1 out_approverPO_apprPO_0) (and (= out_signerGRN_signGRN_1 out_signerGRN_signGRN_0) (and (= out_signerGRN_ctrsignGRN_1 out_signerGRN_ctrsignGRN_0) true))))))))))))))))))
  (forall ((?V Id) (?W Action)) (iff (executed_1 ?V ?W) (or (and (= ?V ?U) (= ?W t1_receive)) (executed_0 ?V ?W))))
  )
  )
   )))
 

;assumption 53
(assert 
 (not (and initial_wf_0 (and initial_pm_0 (t1_receive_0_1 id6))))
 )

(set-info :status sat)
(check-sat)
;; (get-model)