(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :author |Thomas Sturm, CNRS France, http://science.thomas-sturm.de|)
(set-info :source |
Transmitted by: Thomas Sturm
Generated on: 20161105
Received on: 20161105
Generator: RedLog, http://www.redlog.eu/
Application: qualitative analysis of systems of ODE in physics, chemistry, and the life sciences
Publication: Algebraic Biology 2008, doi:10.1007/978-3-540-85101-1_15
Additional information:
All problems have the following form: a certain polynomial has a zero where all variables are positive.  Interval solutions for satisfiable problems is a valuable information.
|)
(set-info :series |MGC - Models of Genetic Circuits|)
(set-info :instance |08|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-const delta Real)
(declare-const alpha Real)
(declare-const mu Real)
(declare-const lambda1 Real)
(declare-const theta Real)
(declare-const gamma0 Real)
(declare-const vv2 Real)
(declare-const vv3 Real)
(declare-const vv1 Real)
(assert (and (and (and (< (- vv1) 0) (< (- vv3) 0)) (< (- vv2) 0)) (and (and (
and (and (and (and (and (= (+ (* gamma0 theta) (- (* theta vv1 (* vv3 vv3 vv3 
vv3 vv3 vv3 vv3 vv3))) (- (* theta vv1))) 0) (= (+ (* gamma0 mu) (* lambda1 vv1)
 (- vv2)) 0)) (= (+ (* 8 alpha gamma0) (- (* 8 alpha vv1 (* vv3 vv3 vv3 vv3 vv3 
vv3 vv3 vv3))) (- (* 8 alpha vv1)) (* delta vv2) (- (* delta vv3))) 0)) (< (+ 
(- (* 8 delta lambda1 theta vv1 (* vv3 vv3 vv3 vv3 vv3 vv3 vv3))) (- (* delta 
theta (* vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3))) (- (* delta theta))) 0) (= (+ (* 
4096 (* alpha alpha) (* vv1 vv1) (* vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3 
vv3 vv3 vv3)) (* 64 alpha delta theta vv1 (* vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3
 vv3 vv3 vv3 vv3 vv3 vv3)) (* 64 alpha delta theta vv1 (* vv3 vv3 vv3 vv3 vv3 
vv3 vv3)) (* 128 alpha delta vv1 (* vv3 vv3 vv3 vv3 vv3 vv3 vv3)) (* 128 alpha 
theta vv1 (* vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3)) (* 
128 alpha theta vv1 (* vv3 vv3 vv3 vv3 vv3 vv3 vv3)) (* 64 alpha vv1 (* vv3 vv3 
vv3 vv3 vv3 vv3 vv3)) (* (* delta delta) theta (* vv3 vv3 vv3 vv3 vv3 vv3 vv3 
vv3)) (* (* delta delta) theta) (* delta delta) (- (* 8 delta lambda1 theta vv1 
(* vv3 vv3 vv3 vv3 vv3 vv3 vv3))) (* delta (* theta theta) (* vv3 vv3 vv3 vv3 
vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3)) (* 2 delta (* theta theta) (* 
vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3)) (* delta (* theta theta)) (* 2 delta theta (* 
vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3)) (* 2 delta theta) delta (* (* theta theta) (* 
vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3)) (* 2 (* theta 
theta) (* vv3 vv3 vv3 vv3 vv3 vv3 vv3 vv3)) (* theta theta) (* theta (* vv3 vv3 
vv3 vv3 vv3 vv3 vv3 vv3)) theta) 0)) (< (- theta) 0)) (< (- gamma0) 0)) (< (- mu
) 0)) (< (- delta) 0)) (< (- alpha) 0)))
(check-sat)
(exit)
