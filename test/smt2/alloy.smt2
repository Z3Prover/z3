
; Copyright (c) 2015 Microsoft Corporation
(set-logic AUFLIA)
(set-option :auto-config true)
(set-option :smt.macro-finder true)
(set-option :produce-unsat-cores true)
;; sorts
(declare-sort Atom)
(declare-sort Rel1)
(declare-sort Rel2)
(declare-sort Rel3)
;; --end sorts

;; functions
(declare-fun left () Rel3)
(declare-fun in_1 (Atom Rel1) Bool)
(declare-fun in_2 (Atom Atom Rel2) Bool)
(declare-fun prod_1x1 (Rel1 Rel1) Rel2)
(declare-fun in_3 (Atom Atom Atom Rel3) Bool)
(declare-fun prod_2x1 (Rel2 Rel1) Rel3)
(declare-fun subset_3 (Rel3 Rel3) Bool)
(declare-fun right () Rel3)
(declare-fun subset_2 (Rel2 Rel2) Bool)
(declare-fun join_1x3 (Rel1 Rel3) Rel2)
(declare-fun a2r_1 (Atom) Rel1)
(declare-fun lone_1 (Rel1) Bool)
(declare-fun marked () Rel2)
(declare-fun subset_1 (Rel1 Rel1) Bool)
(declare-fun join_1x2 (Rel1 Rel2) Rel1)
(declare-fun freeList () Rel2)
(declare-fun disjoint_1 (Rel1 Rel1) Bool)
(declare-fun clearMarks (Rel1 Rel1) Bool)
(declare-fun some_1 (Rel1) Bool)
(declare-fun reachable (Rel1 Rel1) Rel1)
(declare-fun union_2 (Rel2 Rel2) Rel2)
(declare-fun trans (Rel2) Bool)
(declare-fun transClos (Rel2) Rel2)
(declare-fun union_1 (Rel1 Rel1) Rel1)
(declare-fun mark (Rel1 Rel1 Rel1) Bool)
(declare-fun setFreeList (Rel1 Rel1) Bool)
(declare-fun iden () Rel2)
(declare-fun reflTransClos (Rel2) Rel2)
(declare-fun diff_1 (Rel1 Rel1) Rel1)
(declare-fun one_1 (Rel1) Bool)
(declare-fun GC (Rel1 Rel1 Rel1) Bool)
(declare-fun HeapState () Rel1)
(declare-fun Node () Rel1)
;; --end functions

;; axioms
(assert 
 (! 
  (forall ((A Rel1)(B Rel1)(x0 Atom)(y0 Atom)) (= (in_2 x0 y0 (prod_1x1 A B)) (and (in_1 x0 A) (in_1 y0 B)))) 
 :named ax0 
 ) 
 )
(assert 
 (! 
  (forall ((A Rel2)(B Rel1)(x0 Atom)(x1 Atom)(y0 Atom)) (= (in_3 x0 x1 y0 (prod_2x1 A B)) (and (in_2 x0 x1 A) (in_1 y0 B)))) 
 :named ax1 
 ) 
 )
(assert 
 (! 
  (forall ((x Rel3)(y Rel3)) (= (subset_3 x y) (forall ((a0 Atom)(a1 Atom)(a2 Atom)) (=> (in_3 a0 a1 a2 x) (in_3 a0 a1 a2 y))))) 
 :named ax2 
 ) 
 )
(assert 
 (! 
  (forall ((x Rel2)(y Rel2)) (= (subset_2 x y) (forall ((a0 Atom)(a1 Atom)) (=> (in_2 a0 a1 x) (in_2 a0 a1 y))))) 
 :named ax3 
 ) 
 )
(assert 
 (! 
  ; axiom for join_1x3
(forall ((A Rel1)(B Rel3)(y0 Atom)(y1 Atom)) (= (in_2 y0 y1 (join_1x3 A B)) (exists ((x Atom)) (and (in_1 x A) (in_3 x y0 y1 B))))) 
 :named ax4 
 ) 
 )
(assert 
 (! 
  (forall ((x0 Atom)) (and (in_1 x0 (a2r_1 x0)) (forall ((y0 Atom)) (=> (in_1 y0 (a2r_1 x0)) (= x0 y0))))) 
 :named ax5 
 ) 
 )
(assert 
 (! 
  (forall ((X Rel1)) (= (lone_1 X) (forall ((a0 Atom)(b0 Atom)) (=> (and (in_1 a0 X) (in_1 b0 X)) (= a0 b0))))) 
 :named ax6 
 ) 
 )
(assert 
 (! 
  (forall ((x Rel1)(y Rel1)) (= (subset_1 x y) (forall ((a0 Atom)) (=> (in_1 a0 x) (in_1 a0 y))))) 
 :named ax7 
 ) 
 )
(assert 
 (! 
  ; axiom for join_1x2
(forall ((A Rel1)(B Rel2)(y0 Atom)) (= (in_1 y0 (join_1x2 A B)) (exists ((x Atom)) (and (in_1 x A) (in_2 x y0 B))))) 
 :named ax8 
 ) 
 )
(assert 
 (! 
  (forall ((A Rel1)(B Rel1)) (= (disjoint_1 A B) (forall ((a0 Atom)) (=> (in_1 a0 A) (not (in_1 a0 B)))))) 
 :named ax9 
 ) 
 )
(assert 
 (! 
  (forall ((A Rel1)) (= (some_1 A) (exists ((a0 Atom)) (in_1 a0 A)))) 
 :named ax10 
 ) 
 )
(assert 
 (! 
  (forall ((x0 Atom)(x1 Atom)(A Rel2)(B Rel2)) (= (in_2 x0 x1 (union_2 A B)) (or (in_2 x0 x1 A) (in_2 x0 x1 B)))) 
 :named ax11 
 ) 
 )
(assert 
 (! 
  (forall ((r Rel2)) (= (trans r) (forall ((a1 Atom)(a2 Atom)(a3 Atom)) (=> (and (in_2 a1 a2 r) (in_2 a2 a3 r)) (in_2 a1 a3 r))))) 
 :named ax12 
 ) 
 )
(assert 
 (! 
  (forall ((r Rel2)) (subset_2 r (transClos r))) 
 :named ax13 
 ) 
 )
(assert 
 (! 
  (forall ((r Rel2)) (trans (transClos r))) 
 :named ax14 
 ) 
 )
(assert 
 (! 
  (forall ((r1 Rel2)(r2 Rel2)) (=> (and (subset_2 r1 r2) (trans r2)) (subset_2 (transClos r1) r2))) 
 :named ax15 
 ) 
 )
(assert 
 (! 
  (forall ((x0 Atom)(A Rel1)(B Rel1)) (= (in_1 x0 (union_1 A B)) (or (in_1 x0 A) (in_1 x0 B)))) 
 :named ax16 
 ) 
 )
(assert 
 (! 
  (forall ((a0 Atom)) (in_2 a0 a0 iden)) 
 :named ax17 
 ) 
 )
(assert 
 (! 
  (forall ((r Rel2)) (subset_2 r (reflTransClos r))) 
 :named ax18 
 ) 
 )
(assert 
 (! 
  (forall ((r Rel2)) (trans (reflTransClos r))) 
 :named ax19 
 ) 
 )
(assert 
 (! 
  (forall ((r1 Rel2)(r2 Rel2)) (=> (and (subset_2 r1 r2) (trans r2)) (subset_2 (reflTransClos r1) r2))) 
 :named ax20 
 ) 
 )
(assert 
 (! 
  (forall ((r Rel2)) (subset_2 iden (reflTransClos r))) 
 :named ax21 
 ) 
 )
(assert 
 (! 
  (forall ((A Rel1)(B Rel1)(a0 Atom)) (= (in_1 a0 (diff_1 A B)) (and (in_1 a0 A) (not (in_1 a0 B))))) 
 :named ax22 
 ) 
 )
(assert 
 (! 
  (forall ((X Rel1)) (= (one_1 X) (and (exists ((a0 Atom)) (in_1 a0 X)) (forall ((a0 Atom)(b0 Atom)) (=> (and (in_1 a0 X) (in_1 b0 X)) (= a0 b0)))))) 
 :named ax23 
 ) 
 )
;; --end axioms

;; assertions
(assert 
 (! 
  (subset_3 left (prod_2x1 (prod_1x1 HeapState Node) Node)) 
 :named a0 
 ) 
 )
(assert 
 (! 
  (subset_3 right (prod_2x1 (prod_1x1 HeapState Node) Node)) 
 :named a1 
 ) 
 )
(assert 
 (! 
  (forall ((this Atom)) (=> (in_1 this HeapState) (and (forall ((x0 Atom)) (=> (in_1 x0 Node) (lone_1 (join_1x2 (a2r_1 x0) (join_1x3 (a2r_1 this) right))))) (forall ((x0 Atom)) (=> (in_1 x0 Node) (lone_1 (join_1x2 (a2r_1 x0) (join_1x3 (a2r_1 this) left)))))))) 
 :named a2 
 ) 
 )
(assert 
 (! 
  (subset_2 marked (prod_1x1 HeapState Node)) 
 :named a3 
 ) 
 )
(assert 
 (! 
  (subset_2 freeList (prod_1x1 HeapState Node)) 
 :named a4 
 ) 
 )
(assert 
 (! 
  (forall ((this Atom)) (=> (in_1 this HeapState) (lone_1 (join_1x2 (a2r_1 this) freeList)))) 
 :named a5 
 ) 
 )
(assert 
 (! 
  (disjoint_1 HeapState Node) 
 :named a6 
 ) 
 )
(assert 
 (! 
  (forall ((hs Rel1)(hs_ Rel1)) (= (clearMarks hs hs_) (and 
    (not (some_1 (join_1x2 hs_ marked)))
    (= (join_1x3 hs_ left) (join_1x3 hs left))
    (= (join_1x3 hs_ right) (join_1x3 hs right))
  ))) 
 :named a7 
 ) 
 )
(assert 
 (! 
  (forall ((hs Rel1)(n Rel1)) (= (reachable hs n) (union_1 n (join_1x2 n (transClos (union_2 (join_1x3 hs left) (join_1x3 hs right))))))) 
 :named a8 
 ) 
 )
(assert 
 (! 
  (forall ((hs Rel1)(from Rel1)(hs_ Rel1)) (= (mark hs from hs_) (and 
    (= (join_1x2 hs_ marked) (reachable hs from))
    (= (join_1x3 hs_ left) (join_1x3 hs left))
    (= (join_1x3 hs_ right) (join_1x3 hs right))
  ))) 
 :named a9 
 ) 
 )
(assert 
 (! 
  (forall ((hs Rel1)(hs_ Rel1)) (= (setFreeList hs hs_) (and 
    (subset_1 (join_1x2 (join_1x2 hs_ freeList) (reflTransClos (join_1x3 hs_ left))) (diff_1 Node (join_1x2 hs marked)))
    (forall ((n Atom)) (=> (in_1 n Node) (ite (not (in_1 n (join_1x2 hs marked))) (and 
    (not (some_1 (join_1x2 (a2r_1 n) (join_1x3 hs_ right))))
    (subset_1 (join_1x2 (a2r_1 n) (join_1x3 hs_ left)) (join_1x2 (join_1x2 hs_ freeList) (reflTransClos (join_1x3 hs_ left))))
    (in_1 n (join_1x2 (join_1x2 hs_ freeList) (reflTransClos (join_1x3 hs_ left))))
  ) (and (= (join_1x2 (a2r_1 n) (join_1x3 hs_ left)) (join_1x2 (a2r_1 n) (join_1x3 hs left))) (= (join_1x2 (a2r_1 n) (join_1x3 hs_ right)) (join_1x2 (a2r_1 n) (join_1x3 hs right)))))))
    (= (join_1x2 hs_ marked) (join_1x2 hs marked))
  ))) 
 :named a10 
 ) 
 )
(assert 
 (! 
  (forall ((hs Rel1)(root Rel1)(hs_ Rel1)) (= (GC hs root hs_) (exists ((hs1 Atom)(hs2 Atom)) (and 
    (in_1 hs1 HeapState)
    (in_1 hs2 HeapState)
    (and 
    (clearMarks hs (a2r_1 hs1))
    (mark (a2r_1 hs1) root (a2r_1 hs2))
    (setFreeList (a2r_1 hs2) hs_)
  )
  )))) 
 :named a11 
 ) 
 )
;; --end assertions

;; command
; (assert 
; (! 
 ; (not (forall ((h Atom)(h_ Atom)(root Atom)) (=> (and 
   ; (in_1 h HeapState)
   ; (in_1 h_ HeapState)
   ; (in_1 root Node)
 ; ) (=> (GC (a2r_1 h) (a2r_1 root) (a2r_1 h_)) (forall ((live Atom)) (=> (and (in_1 live Node) (in_1 live (reachable (a2r_1 h) (a2r_1 root)))) (and (= (join_1x2 (a2r_1 live) (join_1x3 (a2r_1 h_) left)) (join_1x2 (a2r_1 live) (join_1x3 (a2r_1 h) left))) (= (join_1x2 (a2r_1 live) (join_1x3 (a2r_1 h_) right)) (join_1x2 (a2r_1 live) (join_1x3 (a2r_1 h) right)))))))))) 
; :named c0 
; ) 
;)
;; --end command

;; lemmas
(assert
 (! 
  ; 1. lemma for join_1x3. direction: join to in
(forall ((a2 Atom)(a1 Atom)(a0 Atom)(r Rel3)) (=> (in_2 a1 a0 (join_1x3 ; (swapped)
(a2r_1 a2) r)) (in_3 a2 a1 a0 r))) 
 :named l0 
 ) 
 )
(assert
 (! 
  ; 2. lemma for join_1x3. direction: in to join
(forall ((a2 Atom)(a1 Atom)(a0 Atom)(r Rel3)) (=> (in_3 a2 a1 a0 r) (in_2 a1 a0 (join_1x3 ; (swapped)
(a2r_1 a2) r)))) 
 :named l1 
 ) 
 )
(assert
 (! 
  ; 1. lemma for join_1x2. direction: join to in
(forall ((a1 Atom)(a0 Atom)(r Rel2)) (=> (in_1 a0 (join_1x2 ; (swapped)
(a2r_1 a1) r)) (in_2 a1 a0 r))) 
 :named l2 
 ) 
 )
(assert
 (! 
  ; 2. lemma for join_1x2. direction: in to join
(forall ((a1 Atom)(a0 Atom)(r Rel2)) (=> (in_2 a1 a0 r) (in_1 a0 (join_1x2 ; (swapped)
(a2r_1 a1) r)))) 
 :named l3 
 ) 
 )
(assert
 (! 
  (forall ((a1 Atom)(a2 Atom)(r Rel2)) (=> (in_2 a1 a2 (transClos r)) (exists ((a3 Atom)) (and (in_2 a1 a3 r) (in_2 a3 a2 (transClos r)))))) 
 :named l4 
 ) 
 )
(assert
 (! 
  (forall ((a1 Atom)(a2 Atom)(r Rel2)) (=> (in_2 a1 a2 (transClos r)) (exists ((a3 Atom)) (and (in_2 a1 a3 (transClos r)) (in_2 a3 a2 r))))) 
 :named l5 
 ) 
 )
(assert
 (! 
  (forall ((a1 Atom)(a2 Atom)(r Rel2)) (=> (in_2 a1 a2 (reflTransClos r)) (exists ((a3 Atom)) (and (in_2 a1 a3 r) (in_2 a3 a2 (reflTransClos r)))))) 
 :named l6 
 ) 
 )
(assert
 (! 
  (forall ((a1 Atom)(a2 Atom)(r Rel2)) (=> (in_2 a1 a2 (reflTransClos r)) (exists ((a3 Atom)) (and (in_2 a1 a3 (reflTransClos r)) (in_2 a3 a2 r))))) 
 :named l7 
 ) 
 )
;; --end lemmas

;; -- key stuff for debugging --
;\problem {(
;
;)-> (
;
;;\predicates {

;;}

;; -- END key stuff --
(check-sat)
;; (get-unsat-core)