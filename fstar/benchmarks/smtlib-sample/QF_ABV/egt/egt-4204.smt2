(set-info :smt-lib-version 2.6)
(set-logic QF_ABV)
(set-info :source |
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.

|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun packet () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (not (= (concat (_ bv0 24) (select packet (_ bv240 32))) (_ bv53 32))))
(assert (not (= (concat (_ bv0 24) (select packet (_ bv240 32))) (_ bv0 32))))
(assert (= (concat (_ bv0 24) (select packet (_ bv240 32))) (_ bv52 32)))
(assert (not (= (concat (_ bv0 24) (select packet (bvadd (_ bv242 32) (concat (_ bv0 24) (select packet (_ bv241 32)))))) (_ bv53 32))))
(assert (not (= (concat (_ bv0 24) (select packet (bvadd (_ bv242 32) (concat (_ bv0 24) (select packet (_ bv241 32)))))) (_ bv0 32))))
(assert (= (concat (_ bv0 24) (select packet (bvadd (_ bv242 32) (concat (_ bv0 24) (select packet (_ bv241 32)))))) (_ bv52 32)))
(assert (let ((?v_0 (concat (_ bv0 24) (select packet (_ bv241 32))))) (not (bvsle (_ bv308 32) (bvadd (bvadd (bvadd (_ bv0 32) (bvadd ?v_0 (_ bv2 32))) (_ bv1 32)) (concat (_ bv0 24) (select packet (bvadd (_ bv243 32) ?v_0))))))))
(assert (let ((?v_0 (bvadd (concat (_ bv0 24) (select packet (_ bv241 32))) (_ bv2 32)))) (not (bvsle (_ bv308 32) (bvadd (bvadd (_ bv0 32) ?v_0) ?v_0)))))
(assert (not (= (concat (_ bv0 24) (select packet (bvadd (_ bv244 32) (bvmul (_ bv2 32) (concat (_ bv0 24) (select packet (_ bv241 32))))))) (_ bv53 32))))
(assert (not (= (concat (_ bv0 24) (select packet (bvadd (_ bv244 32) (bvmul (_ bv2 32) (concat (_ bv0 24) (select packet (_ bv241 32))))))) (_ bv0 32))))
(assert (= (concat (_ bv0 24) (select packet (bvadd (_ bv244 32) (bvmul (_ bv2 32) (concat (_ bv0 24) (select packet (_ bv241 32))))))) (_ bv52 32)))
(assert (let ((?v_1 (concat (_ bv0 24) (select packet (_ bv241 32))))) (let ((?v_0 (bvadd ?v_1 (_ bv2 32)))) (not (bvsle (_ bv308 32) (bvadd (bvadd (bvadd (bvadd (_ bv0 32) ?v_0) ?v_0) (_ bv1 32)) (concat (_ bv0 24) (select packet (bvadd (_ bv245 32) (bvmul (_ bv2 32) ?v_1))))))))))
(assert (let ((?v_0 (bvadd (_ bv247 32) (bvmul (_ bv2 32) (concat (_ bv0 24) (select packet (_ bv241 32))))))) (and (bvule (_ bv0 32) ?v_0) (bvule ?v_0 (_ bv547 32)))))
(assert (let ((?v_0 (bvadd (concat (_ bv0 24) (select packet (_ bv241 32))) (_ bv2 32)))) (not (bvsle (_ bv308 32) (bvadd (bvadd (bvadd (_ bv0 32) ?v_0) ?v_0) ?v_0)))))
(assert (not (= (concat (_ bv0 24) (select packet (bvadd (_ bv246 32) (bvmul (_ bv3 32) (concat (_ bv0 24) (select packet (_ bv241 32))))))) (_ bv53 32))))
(assert (let ((?v_0 (bvadd (_ bv246 32) (bvmul (_ bv3 32) (concat (_ bv0 24) (select packet (_ bv241 32))))))) (not (and (bvule (_ bv0 32) ?v_0) (bvule ?v_0 (_ bv547 32))))))
(check-sat)
(exit)
