(set-info :smt-lib-version 2.6)
(set-logic QF_ABV)
(set-info :source |
Ivan Jager <aij+nospam@andrew.cmu.edu>

|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun mem_35_57_4 () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun R_EBX_6_77_3 () (_ BitVec 32))
(declare-fun R_EBP_0_60_2 () (_ BitVec 32))
(declare-fun R_ESP_1_58_1 () (_ BitVec 32))
(assert (let ((?v_5 (bvsub R_ESP_1_58_1 (_ bv4 32)))) (let ((?v_0 (bvsub ?v_5 (_ bv4 32)))) (let ((?v_3 (bvadd (bvadd ?v_0 (_ bv4 32)) (_ bv4 32))) (?v_1 (bvsub (bvsub ?v_0 (_ bv4 32)) (_ bv4 32))) (?v_4 (store (store (store (store mem_35_57_4 (bvadd ?v_0 (_ bv3 32)) ((_ extract 7 0) (bvlshr R_EBP_0_60_2 (_ bv24 32)))) (bvadd ?v_0 (_ bv2 32)) ((_ extract 7 0) (bvlshr R_EBP_0_60_2 (_ bv16 32)))) (bvadd ?v_0 (_ bv1 32)) ((_ extract 7 0) (bvlshr R_EBP_0_60_2 (_ bv8 32)))) (bvadd ?v_0 (_ bv0 32)) ((_ extract 7 0) R_EBP_0_60_2)))) (let ((?v_2 (store (store (store (store ?v_4 (bvadd ?v_1 (_ bv3 32)) ((_ extract 7 0) (bvlshr R_EBX_6_77_3 (_ bv24 32)))) (bvadd ?v_1 (_ bv2 32)) ((_ extract 7 0) (bvlshr R_EBX_6_77_3 (_ bv16 32)))) (bvadd ?v_1 (_ bv1 32)) ((_ extract 7 0) (bvlshr R_EBX_6_77_3 (_ bv8 32)))) (bvadd ?v_1 (_ bv0 32)) ((_ extract 7 0) R_EBX_6_77_3))) (?v_6 (bvadd ?v_5 (_ bv8 32)))) (= (_ bv1 1) (bvand (ite (not (= (bvor (bvor (bvor (concat (_ bv0 24) (select mem_35_57_4 (bvadd R_ESP_1_58_1 (_ bv0 32)))) (bvshl (concat (_ bv0 24) (select mem_35_57_4 (bvadd R_ESP_1_58_1 (_ bv1 32)))) (_ bv8 32))) (bvshl (concat (_ bv0 24) (select mem_35_57_4 (bvadd R_ESP_1_58_1 (_ bv2 32)))) (_ bv16 32))) (bvshl (concat (_ bv0 24) (select mem_35_57_4 (bvadd R_ESP_1_58_1 (_ bv3 32)))) (_ bv24 32))) (bvor (bvor (bvor (concat (_ bv0 24) (select ?v_2 (bvadd ?v_3 (_ bv0 32)))) (bvshl (concat (_ bv0 24) (select ?v_2 (bvadd ?v_3 (_ bv1 32)))) (_ bv8 32))) (bvshl (concat (_ bv0 24) (select ?v_2 (bvadd ?v_3 (_ bv2 32)))) (_ bv16 32))) (bvshl (concat (_ bv0 24) (select ?v_2 (bvadd ?v_3 (_ bv3 32)))) (_ bv24 32))))) (_ bv1 1) (_ bv0 1)) (bvand ((_ extract 0 0) (concat (_ bv0 31) (ite (= (concat (_ bv0 24) ((_ extract 7 0) (concat (_ bv0 24) (select ?v_2 (bvor (bvor (bvor (concat (_ bv0 24) (select ?v_4 (bvadd ?v_6 (_ bv0 32)))) (bvshl (concat (_ bv0 24) (select ?v_4 (bvadd ?v_6 (_ bv1 32)))) (_ bv8 32))) (bvshl (concat (_ bv0 24) (select ?v_4 (bvadd ?v_6 (_ bv2 32)))) (_ bv16 32))) (bvshl (concat (_ bv0 24) (select ?v_4 (bvadd ?v_6 (_ bv3 32)))) (_ bv24 32))))))) (_ bv0 32)) (_ bv1 1) (_ bv0 1)))) (_ bv1 1)))))))))
(check-sat)
(exit)
