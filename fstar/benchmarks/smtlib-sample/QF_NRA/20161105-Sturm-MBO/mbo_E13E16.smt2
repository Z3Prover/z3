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
(set-info :series |MBO - Methylene Blue Oscillator System|)
(set-info :instance |E13E16|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-const j2 Real)
(declare-const h6 Real)
(declare-const h5 Real)
(declare-const h4 Real)
(declare-const h3 Real)
(declare-const h2 Real)
(declare-const h1 Real)
(assert (and (> h1 0) (> h2 0) (> h3 0) (> h4 0) (> h5 0) (> h6 0) (> j2 0) (= 
(+ (* 4 (* h1 h1 h1) (* h2 h2) h3 (* j2 j2 j2 j2)) (* 28 (* h1 h1 h1) (* h2 h2) 
h3 (* j2 j2 j2)) (* 60 (* h1 h1 h1) (* h2 h2) h3 (* j2 j2)) (* 52 (* h1 h1 h1) 
(* h2 h2) h3 j2) (* 16 (* h1 h1 h1) (* h2 h2) h3) (* 4 (* h1 h1 h1) (* h2 h2) h5
 (* j2 j2 j2 j2)) (* 28 (* h1 h1 h1) (* h2 h2) h5 (* j2 j2 j2)) (* 60 (* h1 h1 
h1) (* h2 h2) h5 (* j2 j2)) (* 52 (* h1 h1 h1) (* h2 h2) h5 j2) (* 16 (* h1 h1 
h1) (* h2 h2) h5) (* 2 (* h1 h1 h1) (* h2 h2) h6 (* j2 j2 j2 j2)) (* 16 (* h1 h1
 h1) (* h2 h2) h6 (* j2 j2 j2)) (* 42 (* h1 h1 h1) (* h2 h2) h6 (* j2 j2)) (* 44
 (* h1 h1 h1) (* h2 h2) h6 j2) (* 16 (* h1 h1 h1) (* h2 h2) h6) (* 4 (* h1 h1 h1
) h2 (* h3 h3) (* j2 j2 j2 j2 j2)) (* 44 (* h1 h1 h1) h2 (* h3 h3) (* j2 j2 j2 
j2)) (* 172 (* h1 h1 h1) h2 (* h3 h3) (* j2 j2 j2)) (* 292 (* h1 h1 h1) h2 (* h3
 h3) (* j2 j2)) (* 224 (* h1 h1 h1) h2 (* h3 h3) j2) (* 64 (* h1 h1 h1) h2 (* h3
 h3)) (* 6 (* h1 h1 h1) h2 h3 h4 (* j2 j2 j2 j2)) (* 48 (* h1 h1 h1) h2 h3 h4 
(* j2 j2 j2)) (* 126 (* h1 h1 h1) h2 h3 h4 (* j2 j2)) (* 132 (* h1 h1 h1) h2 h3 
h4 j2) (* 48 (* h1 h1 h1) h2 h3 h4) (* 2 (* h1 h1 h1) h2 h3 h5 (* j2 j2 j2 j2 j2
)) (* 52 (* h1 h1 h1) h2 h3 h5 (* j2 j2 j2 j2)) (* 296 (* h1 h1 h1) h2 h3 h5 (* 
j2 j2 j2)) (* 590 (* h1 h1 h1) h2 h3 h5 (* j2 j2)) (* 472 (* h1 h1 h1) h2 h3 h5 
j2) (* 128 (* h1 h1 h1) h2 h3 h5) (* 10 (* h1 h1 h1) h2 h3 h6 (* j2 j2 j2 j2 j2)
) (* 94 (* h1 h1 h1) h2 h3 h6 (* j2 j2 j2 j2)) (* 324 (* h1 h1 h1) h2 h3 h6 (* 
j2 j2 j2)) (* 520 (* h1 h1 h1) h2 h3 h6 (* j2 j2)) (* 376 (* h1 h1 h1) h2 h3 h6 
j2) (* 96 (* h1 h1 h1) h2 h3 h6) (* 2 (* h1 h1 h1) h2 h4 h5 (* j2 j2 j2 j2)) (* 
22 (* h1 h1 h1) h2 h4 h5 (* j2 j2 j2)) (* 76 (* h1 h1 h1) h2 h4 h5 (* j2 j2)) 
(* 88 (* h1 h1 h1) h2 h4 h5 j2) (* 32 (* h1 h1 h1) h2 h4 h5) (* 3 (* h1 h1 h1) 
h2 h4 h6 (* j2 j2 j2 j2)) (* 23 (* h1 h1 h1) h2 h4 h6 (* j2 j2 j2)) (* 56 (* h1 
h1 h1) h2 h4 h6 (* j2 j2)) (* 52 (* h1 h1 h1) h2 h4 h6 j2) (* 16 (* h1 h1 h1) h2
 h4 h6) (* 10 (* h1 h1 h1) h2 (* h5 h5) (* j2 j2 j2 j2)) (* 68 (* h1 h1 h1) h2 
(* h5 h5) (* j2 j2 j2)) (* 138 (* h1 h1 h1) h2 (* h5 h5) (* j2 j2)) (* 112 (* h1
 h1 h1) h2 (* h5 h5) j2) (* 32 (* h1 h1 h1) h2 (* h5 h5)) (* 13 (* h1 h1 h1) h2 
h5 h6 (* j2 j2 j2 j2)) (* 95 (* h1 h1 h1) h2 h5 h6 (* j2 j2 j2)) (* 218 (* h1 h1
 h1) h2 h5 h6 (* j2 j2)) (* 200 (* h1 h1 h1) h2 h5 h6 j2) (* 64 (* h1 h1 h1) h2 
h5 h6) (* (* h1 h1 h1) h2 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 11 (* h1 h1 h1) h2 
(* h6 h6) (* j2 j2 j2 j2)) (* 46 (* h1 h1 h1) h2 (* h6 h6) (* j2 j2 j2)) (* 92 
(* h1 h1 h1) h2 (* h6 h6) (* j2 j2)) (* 88 (* h1 h1 h1) h2 (* h6 h6) j2) (* 32 
(* h1 h1 h1) h2 (* h6 h6)) (* 4 (* h1 h1 h1) (* h3 h3) h4 (* j2 j2 j2 j2 j2)) 
(* 48 (* h1 h1 h1) (* h3 h3) h4 (* j2 j2 j2 j2)) (* 212 (* h1 h1 h1) (* h3 h3) 
h4 (* j2 j2 j2)) (* 424 (* h1 h1 h1) (* h3 h3) h4 (* j2 j2)) (* 384 (* h1 h1 h1)
 (* h3 h3) h4 j2) (* 128 (* h1 h1 h1) (* h3 h3) h4) (* 18 (* h1 h1 h1) (* h3 h3)
 h5 (* j2 j2 j2 j2 j2)) (* 194 (* h1 h1 h1) (* h3 h3) h5 (* j2 j2 j2 j2)) (* 728
 (* h1 h1 h1) (* h3 h3) h5 (* j2 j2 j2)) (* 1128 (* h1 h1 h1) (* h3 h3) h5 (* j2
 j2)) (* 704 (* h1 h1 h1) (* h3 h3) h5 j2) (* 128 (* h1 h1 h1) (* h3 h3) h5) (* 
4 (* h1 h1 h1) (* h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 52 (* h1 h1 h1) (* h3 h3) 
h6 (* j2 j2 j2 j2 j2)) (* 280 (* h1 h1 h1) (* h3 h3) h6 (* j2 j2 j2 j2)) (* 824 
(* h1 h1 h1) (* h3 h3) h6 (* j2 j2 j2)) (* 1360 (* h1 h1 h1) (* h3 h3) h6 (* j2 
j2)) (* 1024 (* h1 h1 h1) (* h3 h3) h6 j2) (* 256 (* h1 h1 h1) (* h3 h3) h6) (* 
2 (* h1 h1 h1) h3 (* h4 h4) (* j2 j2 j2 j2)) (* 18 (* h1 h1 h1) h3 (* h4 h4) (* 
j2 j2 j2)) (* 56 (* h1 h1 h1) h3 (* h4 h4) (* j2 j2)) (* 72 (* h1 h1 h1) h3 (* 
h4 h4) j2) (* 32 (* h1 h1 h1) h3 (* h4 h4)) (* 20 (* h1 h1 h1) h3 h4 h5 (* j2 j2
 j2 j2)) (* 158 (* h1 h1 h1) h3 h4 h5 (* j2 j2 j2)) (* 402 (* h1 h1 h1) h3 h4 h5
 (* j2 j2)) (* 392 (* h1 h1 h1) h3 h4 h5 j2) (* 128 (* h1 h1 h1) h3 h4 h5) (* 4 
(* h1 h1 h1) h3 h4 h6 (* j2 j2 j2 j2 j2)) (* 44 (* h1 h1 h1) h3 h4 h6 (* j2 j2 
j2 j2)) (* 192 (* h1 h1 h1) h3 h4 h6 (* j2 j2 j2)) (* 408 (* h1 h1 h1) h3 h4 h6 
(* j2 j2)) (* 384 (* h1 h1 h1) h3 h4 h6 j2) (* 128 (* h1 h1 h1) h3 h4 h6) (* 45 
(* h1 h1 h1) h3 (* h5 h5) (* j2 j2 j2 j2)) (* 296 (* h1 h1 h1) h3 (* h5 h5) (* 
j2 j2 j2)) (* 548 (* h1 h1 h1) h3 (* h5 h5) (* j2 j2)) (* 352 (* h1 h1 h1) h3 
(* h5 h5) j2) (* 64 (* h1 h1 h1) h3 (* h5 h5)) (* 25 (* h1 h1 h1) h3 h5 h6 (* j2
 j2 j2 j2 j2)) (* 230 (* h1 h1 h1) h3 h5 h6 (* j2 j2 j2 j2)) (* 786 (* h1 h1 h1)
 h3 h5 h6 (* j2 j2 j2)) (* 1292 (* h1 h1 h1) h3 h5 h6 (* j2 j2)) (* 976 (* h1 h1
 h1) h3 h5 h6 j2) (* 256 (* h1 h1 h1) h3 h5 h6) (* 2 (* h1 h1 h1) h3 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1) h3 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
124 (* h1 h1 h1) h3 (* h6 h6) (* j2 j2 j2 j2)) (* 360 (* h1 h1 h1) h3 (* h6 h6) 
(* j2 j2 j2)) (* 592 (* h1 h1 h1) h3 (* h6 h6) (* j2 j2)) (* 480 (* h1 h1 h1) h3
 (* h6 h6) j2) (* 128 (* h1 h1 h1) h3 (* h6 h6)) (* 3 (* h1 h1 h1) (* h4 h4) h5 
(* j2 j2 j2)) (* 20 (* h1 h1 h1) (* h4 h4) h5 (* j2 j2)) (* 36 (* h1 h1 h1) (* 
h4 h4) h5 j2) (* 16 (* h1 h1 h1) (* h4 h4) h5) (* (* h1 h1 h1) (* h4 h4) h6 (* 
j2 j2 j2 j2)) (* 8 (* h1 h1 h1) (* h4 h4) h6 (* j2 j2 j2)) (* 20 (* h1 h1 h1) 
(* h4 h4) h6 (* j2 j2)) (* 16 (* h1 h1 h1) (* h4 h4) h6 j2) (* 15 (* h1 h1 h1) 
h4 (* h5 h5) (* j2 j2 j2)) (* 82 (* h1 h1 h1) h4 (* h5 h5) (* j2 j2)) (* 96 (* 
h1 h1 h1) h4 (* h5 h5) j2) (* 32 (* h1 h1 h1) h4 (* h5 h5)) (* 10 (* h1 h1 h1) 
h4 h5 h6 (* j2 j2 j2 j2)) (* 73 (* h1 h1 h1) h4 h5 h6 (* j2 j2 j2)) (* 174 (* h1
 h1 h1) h4 h5 h6 (* j2 j2)) (* 184 (* h1 h1 h1) h4 h5 h6 j2) (* 64 (* h1 h1 h1) 
h4 h5 h6) (* (* h1 h1 h1) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 10 (* h1 h1 h1) h4
 (* h6 h6) (* j2 j2 j2 j2)) (* 36 (* h1 h1 h1) h4 (* h6 h6) (* j2 j2 j2)) (* 56 
(* h1 h1 h1) h4 (* h6 h6) (* j2 j2)) (* 32 (* h1 h1 h1) h4 (* h6 h6) j2) (* 25 
(* h1 h1 h1) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 165 (* h1 h1 h1) (* h5 h5) h6 (* 
j2 j2 j2)) (* 316 (* h1 h1 h1) (* h5 h5) h6 (* j2 j2)) (* 240 (* h1 h1 h1) (* h5
 h5) h6 j2) (* 64 (* h1 h1 h1) (* h5 h5) h6) (* 5 (* h1 h1 h1) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 49 (* h1 h1 h1) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 176 (* h1 
h1 h1) h5 (* h6 h6) (* j2 j2 j2)) (* 292 (* h1 h1 h1) h5 (* h6 h6) (* j2 j2)) 
(* 224 (* h1 h1 h1) h5 (* h6 h6) j2) (* 64 (* h1 h1 h1) h5 (* h6 h6)) (* 4 (* h1
 h1) (* h2 h2 h2) h3 (* j2 j2 j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2) h3 (* j2 j2 
j2)) (* 24 (* h1 h1) (* h2 h2 h2) h3 (* j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2) h3 
j2) (* 4 (* h1 h1) (* h2 h2 h2) h3) (* 4 (* h1 h1) (* h2 h2 h2) h5 (* j2 j2 j2 
j2)) (* 16 (* h1 h1) (* h2 h2 h2) h5 (* j2 j2 j2)) (* 24 (* h1 h1) (* h2 h2 h2) 
h5 (* j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2) h5 j2) (* 4 (* h1 h1) (* h2 h2 h2) h5
) (* 2 (* h1 h1) (* h2 h2 h2) h6 (* j2 j2 j2 j2)) (* 10 (* h1 h1) (* h2 h2 h2) 
h6 (* j2 j2 j2)) (* 18 (* h1 h1) (* h2 h2 h2) h6 (* j2 j2)) (* 14 (* h1 h1) (* 
h2 h2 h2) h6 j2) (* 4 (* h1 h1) (* h2 h2 h2) h6) (* 6 (* h1 h1) (* h2 h2) (* h3 
h3) (* j2 j2 j2 j2 j2)) (* 52 (* h1 h1) (* h2 h2) (* h3 h3) (* j2 j2 j2 j2)) (* 
148 (* h1 h1) (* h2 h2) (* h3 h3) (* j2 j2 j2)) (* 192 (* h1 h1) (* h2 h2) (* h3
 h3) (* j2 j2)) (* 118 (* h1 h1) (* h2 h2) (* h3 h3) j2) (* 28 (* h1 h1) (* h2 
h2) (* h3 h3)) (* 10 (* h1 h1) (* h2 h2) h3 h4 (* j2 j2 j2 j2)) (* 62 (* h1 h1) 
(* h2 h2) h3 h4 (* j2 j2 j2)) (* 126 (* h1 h1) (* h2 h2) h3 h4 (* j2 j2)) (* 106
 (* h1 h1) (* h2 h2) h3 h4 j2) (* 32 (* h1 h1) (* h2 h2) h3 h4) (* 6 (* h1 h1) 
(* h2 h2) h3 h5 (* j2 j2 j2 j2 j2)) (* 82 (* h1 h1) (* h2 h2) h3 h5 (* j2 j2 j2 
j2)) (* 268 (* h1 h1) (* h2 h2) h3 h5 (* j2 j2 j2)) (* 366 (* h1 h1) (* h2 h2) 
h3 h5 (* j2 j2)) (* 226 (* h1 h1) (* h2 h2) h3 h5 j2) (* 52 (* h1 h1) (* h2 h2) 
h3 h5) (* 15 (* h1 h1) (* h2 h2) h3 h6 (* j2 j2 j2 j2 j2)) (* 107 (* h1 h1) (* 
h2 h2) h3 h6 (* j2 j2 j2 j2)) (* 279 (* h1 h1) (* h2 h2) h3 h6 (* j2 j2 j2)) (* 
333 (* h1 h1) (* h2 h2) h3 h6 (* j2 j2)) (* 182 (* h1 h1) (* h2 h2) h3 h6 j2) 
(* 36 (* h1 h1) (* h2 h2) h3 h6) (* 6 (* h1 h1) (* h2 h2) h4 h5 (* j2 j2 j2 j2))
 (* 48 (* h1 h1) (* h2 h2) h4 h5 (* j2 j2 j2)) (* 106 (* h1 h1) (* h2 h2) h4 h5 
(* j2 j2)) (* 92 (* h1 h1) (* h2 h2) h4 h5 j2) (* 28 (* h1 h1) (* h2 h2) h4 h5) 
(* 6 (* h1 h1) (* h2 h2) h4 h6 (* j2 j2 j2 j2)) (* 36 (* h1 h1) (* h2 h2) h4 h6 
(* j2 j2 j2)) (* 70 (* h1 h1) (* h2 h2) h4 h6 (* j2 j2)) (* 56 (* h1 h1) (* h2 
h2) h4 h6 j2) (* 16 (* h1 h1) (* h2 h2) h4 h6) (* 2 (* h1 h1) (* h2 h2) (* h5 h5
) (* j2 j2 j2 j2 j2)) (* 26 (* h1 h1) (* h2 h2) (* h5 h5) (* j2 j2 j2 j2)) (* 82
 (* h1 h1) (* h2 h2) (* h5 h5) (* j2 j2 j2)) (* 110 (* h1 h1) (* h2 h2) (* h5 h5
) (* j2 j2)) (* 68 (* h1 h1) (* h2 h2) (* h5 h5) j2) (* 16 (* h1 h1) (* h2 h2) 
(* h5 h5)) (* 3 (* h1 h1) (* h2 h2) h5 h6 (* j2 j2 j2 j2 j2)) (* 40 (* h1 h1) 
(* h2 h2) h5 h6 (* j2 j2 j2 j2)) (* 135 (* h1 h1) (* h2 h2) h5 h6 (* j2 j2 j2)) 
(* 194 (* h1 h1) (* h2 h2) h5 h6 (* j2 j2)) (* 128 (* h1 h1) (* h2 h2) h5 h6 j2)
 (* 32 (* h1 h1) (* h2 h2) h5 h6) (* 2 (* h1 h1) (* h2 h2) (* h6 h6) (* j2 j2 j2
 j2 j2)) (* 18 (* h1 h1) (* h2 h2) (* h6 h6) (* j2 j2 j2 j2)) (* 58 (* h1 h1) 
(* h2 h2) (* h6 h6) (* j2 j2 j2)) (* 86 (* h1 h1) (* h2 h2) (* h6 h6) (* j2 j2))
 (* 60 (* h1 h1) (* h2 h2) (* h6 h6) j2) (* 16 (* h1 h1) (* h2 h2) (* h6 h6)) 
(* 8 (* h1 h1) h2 (* h3 h3 h3) (* j2 j2 j2 j2 j2)) (* 64 (* h1 h1) h2 (* h3 h3 
h3) (* j2 j2 j2 j2)) (* 176 (* h1 h1) h2 (* h3 h3 h3) (* j2 j2 j2)) (* 224 (* h1
 h1) h2 (* h3 h3 h3) (* j2 j2)) (* 136 (* h1 h1) h2 (* h3 h3 h3) j2) (* 32 (* h1
 h1) h2 (* h3 h3 h3)) (* 8 (* h1 h1) h2 (* h3 h3) h4 (* j2 j2 j2 j2 j2)) (* 88 
(* h1 h1) h2 (* h3 h3) h4 (* j2 j2 j2 j2)) (* 336 (* h1 h1) h2 (* h3 h3) h4 (* 
j2 j2 j2)) (* 560 (* h1 h1) h2 (* h3 h3) h4 (* j2 j2)) (* 424 (* h1 h1) h2 (* h3
 h3) h4 j2) (* 120 (* h1 h1) h2 (* h3 h3) h4) (* 2 (* h1 h1) h2 (* h3 h3) h5 (* 
j2 j2 j2 j2 j2 j2)) (* 57 (* h1 h1) h2 (* h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 388 
(* h1 h1) h2 (* h3 h3) h5 (* j2 j2 j2 j2)) (* 995 (* h1 h1) h2 (* h3 h3) h5 (* 
j2 j2 j2)) (* 1164 (* h1 h1) h2 (* h3 h3) h5 (* j2 j2)) (* 622 (* h1 h1) h2 (* 
h3 h3) h5 j2) (* 120 (* h1 h1) h2 (* h3 h3) h5) (* 6 (* h1 h1) h2 (* h3 h3) h6 
(* j2 j2 j2 j2 j2 j2)) (* 88 (* h1 h1) h2 (* h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 
470 (* h1 h1) h2 (* h3 h3) h6 (* j2 j2 j2 j2)) (* 1164 (* h1 h1) h2 (* h3 h3) h6
 (* j2 j2 j2)) (* 1384 (* h1 h1) h2 (* h3 h3) h6 (* j2 j2)) (* 752 (* h1 h1) h2 
(* h3 h3) h6 j2) (* 144 (* h1 h1) h2 (* h3 h3) h6) (* 5 (* h1 h1) h2 h3 (* h4 h4
) (* j2 j2 j2 j2)) (* 42 (* h1 h1) h2 h3 (* h4 h4) (* j2 j2 j2)) (* 113 (* h1 h1
) h2 h3 (* h4 h4) (* j2 j2)) (* 120 (* h1 h1) h2 h3 (* h4 h4) j2) (* 44 (* h1 h1
) h2 h3 (* h4 h4)) (* 4 (* h1 h1) h2 h3 h4 h5 (* j2 j2 j2 j2 j2)) (* 82 (* h1 h1
) h2 h3 h4 h5 (* j2 j2 j2 j2)) (* 424 (* h1 h1) h2 h3 h4 h5 (* j2 j2 j2)) (* 816
 (* h1 h1) h2 h3 h4 h5 (* j2 j2)) (* 650 (* h1 h1) h2 h3 h4 h5 j2) (* 180 (* h1 
h1) h2 h3 h4 h5) (* 10 (* h1 h1) h2 h3 h4 h6 (* j2 j2 j2 j2 j2)) (* 115 (* h1 h1
) h2 h3 h4 h6 (* j2 j2 j2 j2)) (* 452 (* h1 h1) h2 h3 h4 h6 (* j2 j2 j2)) (* 743
 (* h1 h1) h2 h3 h4 h6 (* j2 j2)) (* 528 (* h1 h1) h2 h3 h4 h6 j2) (* 132 (* h1 
h1) h2 h3 h4 h6) (* 18 (* h1 h1) h2 h3 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 197 (* 
h1 h1) h2 h3 (* h5 h5) (* j2 j2 j2 j2)) (* 571 (* h1 h1) h2 h3 (* h5 h5) (* j2 
j2 j2)) (* 692 (* h1 h1) h2 h3 (* h5 h5) (* j2 j2)) (* 372 (* h1 h1) h2 h3 (* h5
 h5) j2) (* 72 (* h1 h1) h2 h3 (* h5 h5)) (* 5 (* h1 h1) h2 h3 h5 h6 (* j2 j2 j2
 j2 j2 j2)) (* 96 (* h1 h1) h2 h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 546 (* h1 h1) h2 
h3 h5 h6 (* j2 j2 j2 j2)) (* 1344 (* h1 h1) h2 h3 h5 h6 (* j2 j2 j2)) (* 1601 
(* h1 h1) h2 h3 h5 h6 (* j2 j2)) (* 904 (* h1 h1) h2 h3 h5 h6 j2) (* 192 (* h1 
h1) h2 h3 h5 h6) (* 4 (* h1 h1) h2 h3 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 52 (* 
h1 h1) h2 h3 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 262 (* h1 h1) h2 h3 (* h6 h6) (* 
j2 j2 j2 j2)) (* 638 (* h1 h1) h2 h3 (* h6 h6) (* j2 j2 j2)) (* 772 (* h1 h1) h2
 h3 (* h6 h6) (* j2 j2)) (* 436 (* h1 h1) h2 h3 (* h6 h6) j2) (* 88 (* h1 h1) h2
 h3 (* h6 h6)) (* (* h1 h1) h2 (* h4 h4) h5 (* j2 j2 j2 j2)) (* 16 (* h1 h1) h2 
(* h4 h4) h5 (* j2 j2 j2)) (* 63 (* h1 h1) h2 (* h4 h4) h5 (* j2 j2)) (* 76 (* 
h1 h1) h2 (* h4 h4) h5 j2) (* 28 (* h1 h1) h2 (* h4 h4) h5) (* 3 (* h1 h1) h2 
(* h4 h4) h6 (* j2 j2 j2 j2)) (* 22 (* h1 h1) h2 (* h4 h4) h6 (* j2 j2 j2)) (* 
47 (* h1 h1) h2 (* h4 h4) h6 (* j2 j2)) (* 32 (* h1 h1) h2 (* h4 h4) h6 j2) (* 4
 (* h1 h1) h2 (* h4 h4) h6) (* 12 (* h1 h1) h2 h4 (* h5 h5) (* j2 j2 j2 j2)) (* 
97 (* h1 h1) h2 h4 (* h5 h5) (* j2 j2 j2)) (* 205 (* h1 h1) h2 h4 (* h5 h5) (* 
j2 j2)) (* 168 (* h1 h1) h2 h4 (* h5 h5) j2) (* 48 (* h1 h1) h2 h4 (* h5 h5)) 
(* 2 (* h1 h1) h2 h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 41 (* h1 h1) h2 h4 h5 h6 (* j2
 j2 j2 j2)) (* 202 (* h1 h1) h2 h4 h5 h6 (* j2 j2 j2)) (* 375 (* h1 h1) h2 h4 h5
 h6 (* j2 j2)) (* 296 (* h1 h1) h2 h4 h5 h6 j2) (* 84 (* h1 h1) h2 h4 h5 h6) (* 
3 (* h1 h1) h2 h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 27 (* h1 h1) h2 h4 (* h6 h6) 
(* j2 j2 j2 j2)) (* 85 (* h1 h1) h2 h4 (* h6 h6) (* j2 j2 j2)) (* 117 (* h1 h1) 
h2 h4 (* h6 h6) (* j2 j2)) (* 68 (* h1 h1) h2 h4 (* h6 h6) j2) (* 12 (* h1 h1) 
h2 h4 (* h6 h6)) (* 10 (* h1 h1) h2 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 38 (* h1 h1
) h2 (* h5 h5 h5) (* j2 j2 j2)) (* 54 (* h1 h1) h2 (* h5 h5 h5) (* j2 j2)) (* 34
 (* h1 h1) h2 (* h5 h5 h5) j2) (* 8 (* h1 h1) h2 (* h5 h5 h5)) (* 10 (* h1 h1) 
h2 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 106 (* h1 h1) h2 (* h5 h5) h6 (* j2 j2 j2
 j2)) (* 314 (* h1 h1) h2 (* h5 h5) h6 (* j2 j2 j2)) (* 406 (* h1 h1) h2 (* h5 
h5) h6 (* j2 j2)) (* 244 (* h1 h1) h2 (* h5 h5) h6 j2) (* 56 (* h1 h1) h2 (* h5 
h5) h6) (* (* h1 h1) h2 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 21 (* h1 h1) h2 
h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 124 (* h1 h1) h2 h5 (* h6 h6) (* j2 j2 j2 j2
)) (* 311 (* h1 h1) h2 h5 (* h6 h6) (* j2 j2 j2)) (* 385 (* h1 h1) h2 h5 (* h6 
h6) (* j2 j2)) (* 234 (* h1 h1) h2 h5 (* h6 h6) j2) (* 56 (* h1 h1) h2 h5 (* h6 
h6)) (* (* h1 h1) h2 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 8 (* h1 h1) h2 (* h6 h6
 h6) (* j2 j2 j2 j2)) (* 25 (* h1 h1) h2 (* h6 h6 h6) (* j2 j2 j2)) (* 38 (* h1 
h1) h2 (* h6 h6 h6) (* j2 j2)) (* 28 (* h1 h1) h2 (* h6 h6 h6) j2) (* 8 (* h1 h1
) h2 (* h6 h6 h6)) (* 8 (* h1 h1) (* h3 h3 h3) h4 (* j2 j2 j2 j2 j2)) (* 72 (* 
h1 h1) (* h3 h3 h3) h4 (* j2 j2 j2 j2)) (* 232 (* h1 h1) (* h3 h3 h3) h4 (* j2 
j2 j2)) (* 344 (* h1 h1) (* h3 h3 h3) h4 (* j2 j2)) (* 240 (* h1 h1) (* h3 h3 h3
) h4 j2) (* 64 (* h1 h1) (* h3 h3 h3) h4) (* 36 (* h1 h1) (* h3 h3 h3) h5 (* j2 
j2 j2 j2 j2)) (* 280 (* h1 h1) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 724 (* h1 h1)
 (* h3 h3 h3) h5 (* j2 j2 j2)) (* 816 (* h1 h1) (* h3 h3 h3) h5 (* j2 j2)) (* 
400 (* h1 h1) (* h3 h3 h3) h5 j2) (* 64 (* h1 h1) (* h3 h3 h3) h5) (* 8 (* h1 h1
) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 80 (* h1 h1) (* h3 h3 h3) h6 (* j2 
j2 j2 j2 j2)) (* 344 (* h1 h1) (* h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 832 (* h1 h1)
 (* h3 h3 h3) h6 (* j2 j2 j2)) (* 1040 (* h1 h1) (* h3 h3 h3) h6 (* j2 j2)) (* 
608 (* h1 h1) (* h3 h3 h3) h6 j2) (* 128 (* h1 h1) (* h3 h3 h3) h6) (* 8 (* h1 
h1) (* h3 h3) (* h4 h4) (* j2 j2 j2 j2)) (* 64 (* h1 h1) (* h3 h3) (* h4 h4) (* 
j2 j2 j2)) (* 168 (* h1 h1) (* h3 h3) (* h4 h4) (* j2 j2)) (* 176 (* h1 h1) (* 
h3 h3) (* h4 h4) j2) (* 64 (* h1 h1) (* h3 h3) (* h4 h4)) (* 12 (* h1 h1) (* h3 
h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 146 (* h1 h1) (* h3 h3) h4 h5 (* j2 j2 j2 j2)) 
(* 602 (* h1 h1) (* h3 h3) h4 h5 (* j2 j2 j2)) (* 1016 (* h1 h1) (* h3 h3) h4 h5
 (* j2 j2)) (* 708 (* h1 h1) (* h3 h3) h4 h5 j2) (* 160 (* h1 h1) (* h3 h3) h4 
h5) (* 12 (* h1 h1) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 136 (* h1 h1) (* h3 
h3) h4 h6 (* j2 j2 j2 j2)) (* 552 (* h1 h1) (* h3 h3) h4 h6 (* j2 j2 j2)) (* 
1020 (* h1 h1) (* h3 h3) h4 h6 (* j2 j2)) (* 784 (* h1 h1) (* h3 h3) h4 h6 j2) 
(* 192 (* h1 h1) (* h3 h3) h4 h6) (* 36 (* h1 h1) (* h3 h3) (* h5 h5) (* j2 j2 
j2 j2 j2)) (* 289 (* h1 h1) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 749 (* h1 h1
) (* h3 h3) (* h5 h5) (* j2 j2 j2)) (* 836 (* h1 h1) (* h3 h3) (* h5 h5) (* j2 
j2)) (* 404 (* h1 h1) (* h3 h3) (* h5 h5) j2) (* 64 (* h1 h1) (* h3 h3) (* h5 h5
)) (* 10 (* h1 h1) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 141 (* h1 h1) (* h3
 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 745 (* h1 h1) (* h3 h3) h5 h6 (* j2 j2 j2 j2))
 (* 1756 (* h1 h1) (* h3 h3) h5 h6 (* j2 j2 j2)) (* 2030 (* h1 h1) (* h3 h3) h5 
h6 (* j2 j2)) (* 1112 (* h1 h1) (* h3 h3) h5 h6 j2) (* 224 (* h1 h1) (* h3 h3) 
h5 h6) (* 6 (* h1 h1) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 70 (* h1 h1)
 (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 316 (* h1 h1) (* h3 h3) (* h6 h6) 
(* j2 j2 j2 j2)) (* 804 (* h1 h1) (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 1032 (* 
h1 h1) (* h3 h3) (* h6 h6) (* j2 j2)) (* 608 (* h1 h1) (* h3 h3) (* h6 h6) j2) 
(* 128 (* h1 h1) (* h3 h3) (* h6 h6)) (* 2 (* h1 h1) h3 (* h4 h4 h4) (* j2 j2 j2
)) (* 10 (* h1 h1) h3 (* h4 h4 h4) (* j2 j2)) (* 16 (* h1 h1) h3 (* h4 h4 h4) j2
) (* 8 (* h1 h1) h3 (* h4 h4 h4)) (* 6 (* h1 h1) h3 (* h4 h4) h5 (* j2 j2 j2 j2)
) (* 59 (* h1 h1) h3 (* h4 h4) h5 (* j2 j2 j2)) (* 171 (* h1 h1) h3 (* h4 h4) h5
 (* j2 j2)) (* 182 (* h1 h1) h3 (* h4 h4) h5 j2) (* 64 (* h1 h1) h3 (* h4 h4) h5
) (* 7 (* h1 h1) h3 (* h4 h4) h6 (* j2 j2 j2 j2)) (* 55 (* h1 h1) h3 (* h4 h4) 
h6 (* j2 j2 j2)) (* 152 (* h1 h1) h3 (* h4 h4) h6 (* j2 j2)) (* 144 (* h1 h1) h3
 (* h4 h4) h6 j2) (* 40 (* h1 h1) h3 (* h4 h4) h6) (* 40 (* h1 h1) h3 h4 (* h5 
h5) (* j2 j2 j2 j2)) (* 255 (* h1 h1) h3 h4 (* h5 h5) (* j2 j2 j2)) (* 492 (* h1
 h1) h3 h4 (* h5 h5) (* j2 j2)) (* 354 (* h1 h1) h3 h4 (* h5 h5) j2) (* 80 (* h1
 h1) h3 h4 (* h5 h5)) (* 12 (* h1 h1) h3 h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 137 (* 
h1 h1) h3 h4 h5 h6 (* j2 j2 j2 j2)) (* 561 (* h1 h1) h3 h4 h5 h6 (* j2 j2 j2)) 
(* 971 (* h1 h1) h3 h4 h5 h6 (* j2 j2)) (* 742 (* h1 h1) h3 h4 h5 h6 j2) (* 192 
(* h1 h1) h3 h4 h5 h6) (* 6 (* h1 h1) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 62 
(* h1 h1) h3 h4 (* h6 h6) (* j2 j2 j2 j2)) (* 236 (* h1 h1) h3 h4 (* h6 h6) (* 
j2 j2 j2)) (* 412 (* h1 h1) h3 h4 (* h6 h6) (* j2 j2)) (* 296 (* h1 h1) h3 h4 
(* h6 h6) j2) (* 64 (* h1 h1) h3 h4 (* h6 h6)) (* 45 (* h1 h1) h3 (* h5 h5 h5) 
(* j2 j2 j2 j2)) (* 161 (* h1 h1) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 200 (* h1 h1)
 h3 (* h5 h5 h5) (* j2 j2)) (* 100 (* h1 h1) h3 (* h5 h5 h5) j2) (* 16 (* h1 h1)
 h3 (* h5 h5 h5)) (* 45 (* h1 h1) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 315 (* 
h1 h1) h3 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 812 (* h1 h1) h3 (* h5 h5) h6 (* j2 
j2 j2)) (* 974 (* h1 h1) h3 (* h5 h5) h6 (* j2 j2)) (* 544 (* h1 h1) h3 (* h5 h5
) h6 j2) (* 112 (* h1 h1) h3 (* h5 h5) h6) (* 5 (* h1 h1) h3 h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 67 (* h1 h1) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 346 (* 
h1 h1) h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 808 (* h1 h1) h3 h5 (* h6 h6) (* j2 
j2 j2)) (* 976 (* h1 h1) h3 h5 (* h6 h6) (* j2 j2)) (* 580 (* h1 h1) h3 h5 (* h6
 h6) j2) (* 128 (* h1 h1) h3 h5 (* h6 h6)) (* 2 (* h1 h1) h3 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 18 (* h1 h1) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 76 (* h1
 h1) h3 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 180 (* h1 h1) h3 (* h6 h6 h6) (* j2 j2 
j2)) (* 232 (* h1 h1) h3 (* h6 h6 h6) (* j2 j2)) (* 144 (* h1 h1) h3 (* h6 h6 h6
) j2) (* 32 (* h1 h1) h3 (* h6 h6 h6)) (* 3 (* h1 h1) (* h4 h4 h4) h5 (* j2 j2))
 (* 8 (* h1 h1) (* h4 h4 h4) h5 j2) (* 4 (* h1 h1) (* h4 h4 h4) h5) (* (* h1 h1)
 (* h4 h4 h4) h6 (* j2 j2 j2)) (* 4 (* h1 h1) (* h4 h4 h4) h6 (* j2 j2)) (* 4 
(* h1 h1) (* h4 h4 h4) h6 j2) (* 6 (* h1 h1) (* h4 h4) (* h5 h5) (* j2 j2 j2)) 
(* 34 (* h1 h1) (* h4 h4) (* h5 h5) (* j2 j2)) (* 44 (* h1 h1) (* h4 h4) (* h5 
h5) j2) (* 16 (* h1 h1) (* h4 h4) (* h5 h5)) (* 3 (* h1 h1) (* h4 h4) h5 h6 (* 
j2 j2 j2 j2)) (* 26 (* h1 h1) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 64 (* h1 h1) (* 
h4 h4) h5 h6 (* j2 j2)) (* 66 (* h1 h1) (* h4 h4) h5 h6 j2) (* 20 (* h1 h1) (* 
h4 h4) h5 h6) (* 2 (* h1 h1) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 13 (* h1 h1
) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 24 (* h1 h1) (* h4 h4) (* h6 h6) (* j2 j2
)) (* 12 (* h1 h1) (* h4 h4) (* h6 h6) j2) (* 15 (* h1 h1) h4 (* h5 h5 h5) (* j2
 j2 j2)) (* 37 (* h1 h1) h4 (* h5 h5 h5) (* j2 j2)) (* 30 (* h1 h1) h4 (* h5 h5 
h5) j2) (* 8 (* h1 h1) h4 (* h5 h5 h5)) (* 20 (* h1 h1) h4 (* h5 h5) h6 (* j2 j2
 j2 j2)) (* 119 (* h1 h1) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 229 (* h1 h1) h4 (* 
h5 h5) h6 (* j2 j2)) (* 178 (* h1 h1) h4 (* h5 h5) h6 j2) (* 48 (* h1 h1) h4 (* 
h5 h5) h6) (* 3 (* h1 h1) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 31 (* h1 h1) h4
 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 113 (* h1 h1) h4 h5 (* h6 h6) (* j2 j2 j2)) 
(* 187 (* h1 h1) h4 h5 (* h6 h6) (* j2 j2)) (* 134 (* h1 h1) h4 h5 (* h6 h6) j2)
 (* 32 (* h1 h1) h4 h5 (* h6 h6)) (* (* h1 h1) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2
)) (* 7 (* h1 h1) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 18 (* h1 h1) h4 (* h6 h6 
h6) (* j2 j2 j2)) (* 20 (* h1 h1) h4 (* h6 h6 h6) (* j2 j2)) (* 8 (* h1 h1) h4 
(* h6 h6 h6) j2) (* 25 (* h1 h1) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 90 (* h1 h1
) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 121 (* h1 h1) (* h5 h5 h5) h6 (* j2 j2)) (* 
72 (* h1 h1) (* h5 h5 h5) h6 j2) (* 16 (* h1 h1) (* h5 h5 h5) h6) (* 10 (* h1 h1
) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 73 (* h1 h1) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 192 (* h1 h1) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 237 (* h1
 h1) (* h5 h5) (* h6 h6) (* j2 j2)) (* 140 (* h1 h1) (* h5 h5) (* h6 h6) j2) (* 
32 (* h1 h1) (* h5 h5) (* h6 h6)) (* 5 (* h1 h1) h5 (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 34 (* h1 h1) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 89 (* h1 h1) h5 (* h6 
h6 h6) (* j2 j2 j2)) (* 112 (* h1 h1) h5 (* h6 h6 h6) (* j2 j2)) (* 68 (* h1 h1)
 h5 (* h6 h6 h6) j2) (* 16 (* h1 h1) h5 (* h6 h6 h6)) (* 2 h1 (* h2 h2 h2) (* h3
 h3) (* j2 j2 j2 j2 j2)) (* 10 h1 (* h2 h2 h2) (* h3 h3) (* j2 j2 j2 j2)) (* 20 
h1 (* h2 h2 h2) (* h3 h3) (* j2 j2 j2)) (* 20 h1 (* h2 h2 h2) (* h3 h3) (* j2 j2
)) (* 10 h1 (* h2 h2 h2) (* h3 h3) j2) (* 2 h1 (* h2 h2 h2) (* h3 h3)) (* 4 h1 
(* h2 h2 h2) h3 h4 (* j2 j2 j2 j2)) (* 16 h1 (* h2 h2 h2) h3 h4 (* j2 j2 j2)) 
(* 24 h1 (* h2 h2 h2) h3 h4 (* j2 j2)) (* 16 h1 (* h2 h2 h2) h3 h4 j2) (* 4 h1 
(* h2 h2 h2) h3 h4) (* 4 h1 (* h2 h2 h2) h3 h5 (* j2 j2 j2 j2 j2)) (* 20 h1 (* 
h2 h2 h2) h3 h5 (* j2 j2 j2 j2)) (* 40 h1 (* h2 h2 h2) h3 h5 (* j2 j2 j2)) (* 40
 h1 (* h2 h2 h2) h3 h5 (* j2 j2)) (* 20 h1 (* h2 h2 h2) h3 h5 j2) (* 4 h1 (* h2 
h2 h2) h3 h5) (* 5 h1 (* h2 h2 h2) h3 h6 (* j2 j2 j2 j2 j2)) (* 24 h1 (* h2 h2 
h2) h3 h6 (* j2 j2 j2 j2)) (* 44 h1 (* h2 h2 h2) h3 h6 (* j2 j2 j2)) (* 38 h1 
(* h2 h2 h2) h3 h6 (* j2 j2)) (* 15 h1 (* h2 h2 h2) h3 h6 j2) (* 2 h1 (* h2 h2 
h2) h3 h6) (* 4 h1 (* h2 h2 h2) h4 h5 (* j2 j2 j2 j2)) (* 16 h1 (* h2 h2 h2) h4 
h5 (* j2 j2 j2)) (* 24 h1 (* h2 h2 h2) h4 h5 (* j2 j2)) (* 16 h1 (* h2 h2 h2) h4
 h5 j2) (* 4 h1 (* h2 h2 h2) h4 h5) (* 3 h1 (* h2 h2 h2) h4 h6 (* j2 j2 j2 j2)) 
(* 11 h1 (* h2 h2 h2) h4 h6 (* j2 j2 j2)) (* 15 h1 (* h2 h2 h2) h4 h6 (* j2 j2))
 (* 9 h1 (* h2 h2 h2) h4 h6 j2) (* 2 h1 (* h2 h2 h2) h4 h6) (* 2 h1 (* h2 h2 h2)
 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 10 h1 (* h2 h2 h2) (* h5 h5) (* j2 j2 j2 j2)) 
(* 20 h1 (* h2 h2 h2) (* h5 h5) (* j2 j2 j2)) (* 20 h1 (* h2 h2 h2) (* h5 h5) 
(* j2 j2)) (* 10 h1 (* h2 h2 h2) (* h5 h5) j2) (* 2 h1 (* h2 h2 h2) (* h5 h5)) 
(* 3 h1 (* h2 h2 h2) h5 h6 (* j2 j2 j2 j2 j2)) (* 16 h1 (* h2 h2 h2) h5 h6 (* j2
 j2 j2 j2)) (* 34 h1 (* h2 h2 h2) h5 h6 (* j2 j2 j2)) (* 36 h1 (* h2 h2 h2) h5 
h6 (* j2 j2)) (* 19 h1 (* h2 h2 h2) h5 h6 j2) (* 4 h1 (* h2 h2 h2) h5 h6) (* h1 
(* h2 h2 h2) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6 h1 (* h2 h2 h2) (* h6 h6) (* j2 
j2 j2 j2)) (* 14 h1 (* h2 h2 h2) (* h6 h6) (* j2 j2 j2)) (* 16 h1 (* h2 h2 h2) 
(* h6 h6) (* j2 j2)) (* 9 h1 (* h2 h2 h2) (* h6 h6) j2) (* 2 h1 (* h2 h2 h2) (* 
h6 h6)) (* 4 h1 (* h2 h2) (* h3 h3 h3) (* j2 j2 j2 j2 j2)) (* 20 h1 (* h2 h2) 
(* h3 h3 h3) (* j2 j2 j2 j2)) (* 40 h1 (* h2 h2) (* h3 h3 h3) (* j2 j2 j2)) (* 
40 h1 (* h2 h2) (* h3 h3 h3) (* j2 j2)) (* 20 h1 (* h2 h2) (* h3 h3 h3) j2) (* 4
 h1 (* h2 h2) (* h3 h3 h3)) (* 5 h1 (* h2 h2) (* h3 h3) h4 (* j2 j2 j2 j2 j2)) 
(* 46 h1 (* h2 h2) (* h3 h3) h4 (* j2 j2 j2 j2)) (* 134 h1 (* h2 h2) (* h3 h3) 
h4 (* j2 j2 j2)) (* 176 h1 (* h2 h2) (* h3 h3) h4 (* j2 j2)) (* 109 h1 (* h2 h2)
 (* h3 h3) h4 j2) (* 26 h1 (* h2 h2) (* h3 h3) h4) (* 3 h1 (* h2 h2) (* h3 h3) 
h5 (* j2 j2 j2 j2 j2 j2)) (* 39 h1 (* h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2)) 
(* 147 h1 (* h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2)) (* 253 h1 (* h2 h2) (* h3 h3) 
h5 (* j2 j2 j2)) (* 222 h1 (* h2 h2) (* h3 h3) h5 (* j2 j2)) (* 96 h1 (* h2 h2) 
(* h3 h3) h5 j2) (* 16 h1 (* h2 h2) (* h3 h3) h5) (* 2 h1 (* h2 h2) (* h3 h3) h6
 (* j2 j2 j2 j2 j2 j2)) (* 41 h1 (* h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 
182 h1 (* h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2)) (* 338 h1 (* h2 h2) (* h3 h3) h6 
(* j2 j2 j2)) (* 302 h1 (* h2 h2) (* h3 h3) h6 (* j2 j2)) (* 125 h1 (* h2 h2) 
(* h3 h3) h6 j2) (* 18 h1 (* h2 h2) (* h3 h3) h6) (* 4 h1 (* h2 h2) h3 (* h4 h4)
 (* j2 j2 j2 j2)) (* 26 h1 (* h2 h2) h3 (* h4 h4) (* j2 j2 j2)) (* 54 h1 (* h2 
h2) h3 (* h4 h4) (* j2 j2)) (* 46 h1 (* h2 h2) h3 (* h4 h4) j2) (* 14 h1 (* h2 
h2) h3 (* h4 h4)) (* 6 h1 (* h2 h2) h3 h4 h5 (* j2 j2 j2 j2 j2)) (* 70 h1 (* h2 
h2) h3 h4 h5 (* j2 j2 j2 j2)) (* 222 h1 (* h2 h2) h3 h4 h5 (* j2 j2 j2)) (* 302 
h1 (* h2 h2) h3 h4 h5 (* j2 j2)) (* 188 h1 (* h2 h2) h3 h4 h5 j2) (* 44 h1 (* h2
 h2) h3 h4 h5) (* 8 h1 (* h2 h2) h3 h4 h6 (* j2 j2 j2 j2 j2)) (* 76 h1 (* h2 h2)
 h3 h4 h6 (* j2 j2 j2 j2)) (* 216 h1 (* h2 h2) h3 h4 h6 (* j2 j2 j2)) (* 268 h1 
(* h2 h2) h3 h4 h6 (* j2 j2)) (* 152 h1 (* h2 h2) h3 h4 h6 j2) (* 32 h1 (* h2 h2
) h3 h4 h6) (* h1 (* h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 28 h1 (* h2 
h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 120 h1 (* h2 h2) h3 (* h5 h5) (* j2 j2 
j2 j2)) (* 216 h1 (* h2 h2) h3 (* h5 h5) (* j2 j2 j2)) (* 193 h1 (* h2 h2) h3 
(* h5 h5) (* j2 j2)) (* 84 h1 (* h2 h2) h3 (* h5 h5) j2) (* 14 h1 (* h2 h2) h3 
(* h5 h5)) (* 7 h1 (* h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 80 h1 (* h2 h2) 
h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 301 h1 (* h2 h2) h3 h5 h6 (* j2 j2 j2 j2)) (* 
534 h1 (* h2 h2) h3 h5 h6 (* j2 j2 j2)) (* 490 h1 (* h2 h2) h3 h5 h6 (* j2 j2)) 
(* 224 h1 (* h2 h2) h3 h5 h6 j2) (* 40 h1 (* h2 h2) h3 h5 h6) (* 2 h1 (* h2 h2) 
h3 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 30 h1 (* h2 h2) h3 (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 132 h1 (* h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2)) (* 254 h1 (* h2 h2) h3
 (* h6 h6) (* j2 j2 j2)) (* 240 h1 (* h2 h2) h3 (* h6 h6) (* j2 j2)) (* 108 h1 
(* h2 h2) h3 (* h6 h6) j2) (* 18 h1 (* h2 h2) h3 (* h6 h6)) (* 2 h1 (* h2 h2) 
(* h4 h4) h5 (* j2 j2 j2 j2)) (* 19 h1 (* h2 h2) (* h4 h4) h5 (* j2 j2 j2)) (* 
44 h1 (* h2 h2) (* h4 h4) h5 (* j2 j2)) (* 39 h1 (* h2 h2) (* h4 h4) h5 j2) (* 
12 h1 (* h2 h2) (* h4 h4) h5) (* 3 h1 (* h2 h2) (* h4 h4) h6 (* j2 j2 j2 j2)) 
(* 17 h1 (* h2 h2) (* h4 h4) h6 (* j2 j2 j2)) (* 27 h1 (* h2 h2) (* h4 h4) h6 
(* j2 j2)) (* 15 h1 (* h2 h2) (* h4 h4) h6 j2) (* 2 h1 (* h2 h2) (* h4 h4) h6) 
(* h1 (* h2 h2) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 20 h1 (* h2 h2) h4 (* h5 h5)
 (* j2 j2 j2 j2)) (* 68 h1 (* h2 h2) h4 (* h5 h5) (* j2 j2 j2)) (* 94 h1 (* h2 
h2) h4 (* h5 h5) (* j2 j2)) (* 59 h1 (* h2 h2) h4 (* h5 h5) j2) (* 14 h1 (* h2 
h2) h4 (* h5 h5)) (* 4 h1 (* h2 h2) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 44 h1 (* h2 
h2) h4 h5 h6 (* j2 j2 j2 j2)) (* 134 h1 (* h2 h2) h4 h5 h6 (* j2 j2 j2)) (* 178 
h1 (* h2 h2) h4 h5 h6 (* j2 j2)) (* 110 h1 (* h2 h2) h4 h5 h6 j2) (* 26 h1 (* h2
 h2) h4 h5 h6) (* 3 h1 (* h2 h2) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 21 h1 (* h2
 h2) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 49 h1 (* h2 h2) h4 (* h6 h6) (* j2 j2 j2))
 (* 51 h1 (* h2 h2) h4 (* h6 h6) (* j2 j2)) (* 24 h1 (* h2 h2) h4 (* h6 h6) j2) 
(* 4 h1 (* h2 h2) h4 (* h6 h6)) (* 2 h1 (* h2 h2) (* h5 h5 h5) (* j2 j2 j2 j2 j2
)) (* 10 h1 (* h2 h2) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 20 h1 (* h2 h2) (* h5 h5 
h5) (* j2 j2 j2)) (* 20 h1 (* h2 h2) (* h5 h5 h5) (* j2 j2)) (* 10 h1 (* h2 h2) 
(* h5 h5 h5) j2) (* 2 h1 (* h2 h2) (* h5 h5 h5)) (* h1 (* h2 h2) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 20 h1 (* h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 84
 h1 (* h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 156 h1 (* h2 h2) (* h5 h5) h6 (* 
j2 j2 j2)) (* 149 h1 (* h2 h2) (* h5 h5) h6 (* j2 j2)) (* 72 h1 (* h2 h2) (* h5 
h5) h6 j2) (* 14 h1 (* h2 h2) (* h5 h5) h6) (* 2 h1 (* h2 h2) h5 (* h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 23 h1 (* h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 86 h1 
(* h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 154 h1 (* h2 h2) h5 (* h6 h6) (* j2 
j2 j2)) (* 146 h1 (* h2 h2) h5 (* h6 h6) (* j2 j2)) (* 71 h1 (* h2 h2) h5 (* h6 
h6) j2) (* 14 h1 (* h2 h2) h5 (* h6 h6)) (* h1 (* h2 h2) (* h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 6 h1 (* h2 h2) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 14 h1 (* h2 h2) 
(* h6 h6 h6) (* j2 j2 j2)) (* 16 h1 (* h2 h2) (* h6 h6 h6) (* j2 j2)) (* 9 h1 
(* h2 h2) (* h6 h6 h6) j2) (* 2 h1 (* h2 h2) (* h6 h6 h6)) (* 8 h1 h2 (* h3 h3 
h3) h4 (* j2 j2 j2 j2 j2)) (* 64 h1 h2 (* h3 h3 h3) h4 (* j2 j2 j2 j2)) (* 176 
h1 h2 (* h3 h3 h3) h4 (* j2 j2 j2)) (* 224 h1 h2 (* h3 h3 h3) h4 (* j2 j2)) (* 
136 h1 h2 (* h3 h3 h3) h4 j2) (* 32 h1 h2 (* h3 h3 h3) h4) (* 4 h1 h2 (* h3 h3 
h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 50 h1 h2 (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) 
(* 182 h1 h2 (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 298 h1 h2 (* h3 h3 h3) h5 (* j2
 j2 j2)) (* 242 h1 h2 (* h3 h3 h3) h5 (* j2 j2)) (* 92 h1 h2 (* h3 h3 h3) h5 j2)
 (* 12 h1 h2 (* h3 h3 h3) h5) (* 4 h1 h2 (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 52 h1 h2 (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 228 h1 h2 (* h3 h3 h3) h6 (* 
j2 j2 j2 j2)) (* 436 h1 h2 (* h3 h3 h3) h6 (* j2 j2 j2)) (* 400 h1 h2 (* h3 h3 
h3) h6 (* j2 j2)) (* 168 h1 h2 (* h3 h3 h3) h6 j2) (* 24 h1 h2 (* h3 h3 h3) h6) 
(* 12 h1 h2 (* h3 h3) (* h4 h4) (* j2 j2 j2 j2)) (* 72 h1 h2 (* h3 h3) (* h4 h4)
 (* j2 j2 j2)) (* 144 h1 h2 (* h3 h3) (* h4 h4) (* j2 j2)) (* 120 h1 h2 (* h3 h3
) (* h4 h4) j2) (* 36 h1 h2 (* h3 h3) (* h4 h4)) (* 22 h1 h2 (* h3 h3) h4 h5 (* 
j2 j2 j2 j2 j2)) (* 197 h1 h2 (* h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 570 h1 h2 (* 
h3 h3) h4 h5 (* j2 j2 j2)) (* 727 h1 h2 (* h3 h3) h4 h5 (* j2 j2)) (* 422 h1 h2 
(* h3 h3) h4 h5 j2) (* 90 h1 h2 (* h3 h3) h4 h5) (* 20 h1 h2 (* h3 h3) h4 h6 (* 
j2 j2 j2 j2 j2)) (* 184 h1 h2 (* h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 542 h1 h2 (* 
h3 h3) h4 h6 (* j2 j2 j2)) (* 692 h1 h2 (* h3 h3) h4 h6 (* j2 j2)) (* 394 h1 h2 
(* h3 h3) h4 h6 j2) (* 80 h1 h2 (* h3 h3) h4 h6) (* 4 h1 h2 (* h3 h3) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 73 h1 h2 (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
300 h1 h2 (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 522 h1 h2 (* h3 h3) (* h5 h5) 
(* j2 j2 j2)) (* 435 h1 h2 (* h3 h3) (* h5 h5) (* j2 j2)) (* 166 h1 h2 (* h3 h3)
 (* h5 h5) j2) (* 22 h1 h2 (* h3 h3) (* h5 h5)) (* 18 h1 h2 (* h3 h3) h5 h6 (* 
j2 j2 j2 j2 j2 j2)) (* 204 h1 h2 (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 758 h1 
h2 (* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 1330 h1 h2 (* h3 h3) h5 h6 (* j2 j2 j2)) 
(* 1188 h1 h2 (* h3 h3) h5 h6 (* j2 j2)) (* 512 h1 h2 (* h3 h3) h5 h6 j2) (* 82 
h1 h2 (* h3 h3) h5 h6) (* 8 h1 h2 (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
77 h1 h2 (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 323 h1 h2 (* h3 h3) (* h6 h6
) (* j2 j2 j2 j2)) (* 633 h1 h2 (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 609 h1 h2 
(* h3 h3) (* h6 h6) (* j2 j2)) (* 274 h1 h2 (* h3 h3) (* h6 h6) j2) (* 44 h1 h2 
(* h3 h3) (* h6 h6)) (* 3 h1 h2 h3 (* h4 h4 h4) (* j2 j2 j2)) (* 12 h1 h2 h3 (* 
h4 h4 h4) (* j2 j2)) (* 15 h1 h2 h3 (* h4 h4 h4) j2) (* 6 h1 h2 h3 (* h4 h4 h4))
 (* 13 h1 h2 h3 (* h4 h4) h5 (* j2 j2 j2 j2)) (* 97 h1 h2 h3 (* h4 h4) h5 (* j2 
j2 j2)) (* 216 h1 h2 h3 (* h4 h4) h5 (* j2 j2)) (* 186 h1 h2 h3 (* h4 h4) h5 j2)
 (* 54 h1 h2 h3 (* h4 h4) h5) (* 14 h1 h2 h3 (* h4 h4) h6 (* j2 j2 j2 j2)) (* 92
 h1 h2 h3 (* h4 h4) h6 (* j2 j2 j2)) (* 168 h1 h2 h3 (* h4 h4) h6 (* j2 j2)) (* 
114 h1 h2 h3 (* h4 h4) h6 j2) (* 24 h1 h2 h3 (* h4 h4) h6) (* 8 h1 h2 h3 h4 (* 
h5 h5) (* j2 j2 j2 j2 j2)) (* 102 h1 h2 h3 h4 (* h5 h5) (* j2 j2 j2 j2)) (* 326 
h1 h2 h3 h4 (* h5 h5) (* j2 j2 j2)) (* 430 h1 h2 h3 h4 (* h5 h5) (* j2 j2)) (* 
252 h1 h2 h3 h4 (* h5 h5) j2) (* 54 h1 h2 h3 h4 (* h5 h5)) (* 25 h1 h2 h3 h4 h5 
h6 (* j2 j2 j2 j2 j2)) (* 230 h1 h2 h3 h4 h5 h6 (* j2 j2 j2 j2)) (* 665 h1 h2 h3
 h4 h5 h6 (* j2 j2 j2)) (* 859 h1 h2 h3 h4 h5 h6 (* j2 j2)) (* 511 h1 h2 h3 h4 
h5 h6 j2) (* 112 h1 h2 h3 h4 h5 h6) (* 12 h1 h2 h3 h4 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 103 h1 h2 h3 h4 (* h6 h6) (* j2 j2 j2 j2)) (* 281 h1 h2 h3 h4 (* h6 h6) 
(* j2 j2 j2)) (* 329 h1 h2 h3 h4 (* h6 h6) (* j2 j2)) (* 169 h1 h2 h3 h4 (* h6 
h6) j2) (* 30 h1 h2 h3 h4 (* h6 h6)) (* 16 h1 h2 h3 (* h5 h5 h5) (* j2 j2 j2 j2 
j2)) (* 74 h1 h2 h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 132 h1 h2 h3 (* h5 h5 h5) 
(* j2 j2 j2)) (* 112 h1 h2 h3 (* h5 h5 h5) (* j2 j2)) (* 44 h1 h2 h3 (* h5 h5 h5
) j2) (* 6 h1 h2 h3 (* h5 h5 h5)) (* 9 h1 h2 h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 112 h1 h2 h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 431 h1 h2 h3 (* h5 h5) 
h6 (* j2 j2 j2 j2)) (* 763 h1 h2 h3 (* h5 h5) h6 (* j2 j2 j2)) (* 688 h1 h2 h3 
(* h5 h5) h6 (* j2 j2)) (* 305 h1 h2 h3 (* h5 h5) h6 j2) (* 52 h1 h2 h3 (* h5 h5
) h6) (* 10 h1 h2 h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 116 h1 h2 h3 h5 (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 434 h1 h2 h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 771 
h1 h2 h3 h5 (* h6 h6) (* j2 j2 j2)) (* 712 h1 h2 h3 h5 (* h6 h6) (* j2 j2)) (* 
327 h1 h2 h3 h5 (* h6 h6) j2) (* 58 h1 h2 h3 h5 (* h6 h6)) (* 2 h1 h2 h3 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 20 h1 h2 h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 80 h1 h2 h3 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 156 h1 h2 h3 (* h6 h6 h6) (* j2 
j2 j2)) (* 154 h1 h2 h3 (* h6 h6 h6) (* j2 j2)) (* 72 h1 h2 h3 (* h6 h6 h6) j2) 
(* 12 h1 h2 h3 (* h6 h6 h6)) (* h1 h2 (* h4 h4 h4) h5 (* j2 j2 j2)) (* 7 h1 h2 
(* h4 h4 h4) h5 (* j2 j2)) (* 10 h1 h2 (* h4 h4 h4) h5 j2) (* 4 h1 h2 (* h4 h4 
h4) h5) (* 2 h1 h2 (* h4 h4 h4) h6 (* j2 j2 j2)) (* 6 h1 h2 (* h4 h4 h4) h6 (* 
j2 j2)) (* 4 h1 h2 (* h4 h4 h4) h6 j2) (* 2 h1 h2 (* h4 h4) (* h5 h5) (* j2 j2 
j2 j2)) (* 22 h1 h2 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 52 h1 h2 (* h4 h4) (* 
h5 h5) (* j2 j2)) (* 46 h1 h2 (* h4 h4) (* h5 h5) j2) (* 14 h1 h2 (* h4 h4) (* 
h5 h5)) (* 7 h1 h2 (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 44 h1 h2 (* h4 h4) h5 h6 
(* j2 j2 j2)) (* 85 h1 h2 (* h4 h4) h5 h6 (* j2 j2)) (* 64 h1 h2 (* h4 h4) h5 h6
 j2) (* 16 h1 h2 (* h4 h4) h5 h6) (* 4 h1 h2 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)
) (* 20 h1 h2 (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 28 h1 h2 (* h4 h4) (* h6 h6) 
(* j2 j2)) (* 12 h1 h2 (* h4 h4) (* h6 h6) j2) (* 10 h1 h2 h4 (* h5 h5 h5) (* j2
 j2 j2 j2)) (* 38 h1 h2 h4 (* h5 h5 h5) (* j2 j2 j2)) (* 54 h1 h2 h4 (* h5 h5 h5
) (* j2 j2)) (* 34 h1 h2 h4 (* h5 h5 h5) j2) (* 8 h1 h2 h4 (* h5 h5 h5)) (* 4 h1
 h2 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 50 h1 h2 h4 (* h5 h5) h6 (* j2 j2 j2 
j2)) (* 156 h1 h2 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 208 h1 h2 h4 (* h5 h5) h6 (* 
j2 j2)) (* 128 h1 h2 h4 (* h5 h5) h6 j2) (* 30 h1 h2 h4 (* h5 h5) h6) (* 7 h1 h2
 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 52 h1 h2 h4 h5 (* h6 h6) (* j2 j2 j2 j2)
) (* 137 h1 h2 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 166 h1 h2 h4 h5 (* h6 h6) (* j2 
j2)) (* 94 h1 h2 h4 h5 (* h6 h6) j2) (* 20 h1 h2 h4 h5 (* h6 h6)) (* 2 h1 h2 h4 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 12 h1 h2 h4 (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 26 h1 h2 h4 (* h6 h6 h6) (* j2 j2 j2)) (* 24 h1 h2 h4 (* h6 h6 h6) (* j2 j2))
 (* 8 h1 h2 h4 (* h6 h6 h6) j2) (* 10 h1 h2 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 48 h1 h2 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 92 h1 h2 (* h5 h5 h5) h6 (* j2 
j2 j2)) (* 88 h1 h2 (* h5 h5 h5) h6 (* j2 j2)) (* 42 h1 h2 (* h5 h5 h5) h6 j2) 
(* 8 h1 h2 (* h5 h5 h5) h6) (* 2 h1 h2 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 26 h1 h2 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 100 h1 h2 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 180 h1 h2 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 170 h1
 h2 (* h5 h5) (* h6 h6) (* j2 j2)) (* 82 h1 h2 (* h5 h5) (* h6 h6) j2) (* 16 h1 
h2 (* h5 h5) (* h6 h6)) (* h1 h2 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12 h1
 h2 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 46 h1 h2 h5 (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 84 h1 h2 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 81 h1 h2 h5 (* h6 h6 h6) (* j2
 j2)) (* 40 h1 h2 h5 (* h6 h6 h6) j2) (* 8 h1 h2 h5 (* h6 h6 h6)) (* 8 h1 (* h3 
h3 h3) (* h4 h4) (* j2 j2 j2 j2)) (* 40 h1 (* h3 h3 h3) (* h4 h4) (* j2 j2 j2)) 
(* 72 h1 (* h3 h3 h3) (* h4 h4) (* j2 j2)) (* 56 h1 (* h3 h3 h3) (* h4 h4) j2) 
(* 16 h1 (* h3 h3 h3) (* h4 h4)) (* 16 h1 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2))
 (* 128 h1 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 344 h1 (* h3 h3 h3) h4 h5 (* 
j2 j2 j2)) (* 400 h1 (* h3 h3 h3) h4 h5 (* j2 j2)) (* 200 h1 (* h3 h3 h3) h4 h5 
j2) (* 32 h1 (* h3 h3 h3) h4 h5) (* 8 h1 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) 
(* 88 h1 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 312 h1 (* h3 h3 h3) h4 h6 (* j2 
j2 j2)) (* 440 h1 (* h3 h3 h3) h4 h6 (* j2 j2)) (* 256 h1 (* h3 h3 h3) h4 h6 j2)
 (* 48 h1 (* h3 h3 h3) h4 h6) (* 36 h1 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)
) (* 172 h1 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 298 h1 (* h3 h3 h3) (* h5
 h5) (* j2 j2 j2)) (* 226 h1 (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 72 h1 (* h3 h3
 h3) (* h5 h5) j2) (* 8 h1 (* h3 h3 h3) (* h5 h5)) (* 12 h1 (* h3 h3 h3) h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 102 h1 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 392 
h1 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 730 h1 (* h3 h3 h3) h5 h6 (* j2 j2 j2)
) (* 640 h1 (* h3 h3 h3) h5 h6 (* j2 j2)) (* 244 h1 (* h3 h3 h3) h5 h6 j2) (* 32
 h1 (* h3 h3 h3) h5 h6) (* 4 h1 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 40 h1 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 164 h1 (* h3 h3 h3) (* h6
 h6) (* j2 j2 j2 j2)) (* 376 h1 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 408 h1 
(* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 192 h1 (* h3 h3 h3) (* h6 h6) j2) (* 32 h1 
(* h3 h3 h3) (* h6 h6)) (* 4 h1 (* h3 h3) (* h4 h4 h4) (* j2 j2 j2)) (* 16 h1 
(* h3 h3) (* h4 h4 h4) (* j2 j2)) (* 20 h1 (* h3 h3) (* h4 h4 h4) j2) (* 8 h1 
(* h3 h3) (* h4 h4 h4)) (* 16 h1 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 106 
h1 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 218 h1 (* h3 h3) (* h4 h4) h5 (* j2 
j2)) (* 168 h1 (* h3 h3) (* h4 h4) h5 j2) (* 40 h1 (* h3 h3) (* h4 h4) h5) (* 12
 h1 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 84 h1 (* h3 h3) (* h4 h4) h6 (* 
j2 j2 j2)) (* 192 h1 (* h3 h3) (* h4 h4) h6 (* j2 j2)) (* 152 h1 (* h3 h3) (* h4
 h4) h6 j2) (* 32 h1 (* h3 h3) (* h4 h4) h6) (* 12 h1 (* h3 h3) h4 (* h5 h5) (* 
j2 j2 j2 j2 j2)) (* 118 h1 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 340 h1 (* 
h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 403 h1 (* h3 h3) h4 (* h5 h5) (* j2 j2)) 
(* 201 h1 (* h3 h3) h4 (* h5 h5) j2) (* 32 h1 (* h3 h3) h4 (* h5 h5)) (* 26 h1 
(* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 231 h1 (* h3 h3) h4 h5 h6 (* j2 j2 j2 
j2)) (* 689 h1 (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 896 h1 (* h3 h3) h4 h5 h6 (* 
j2 j2)) (* 508 h1 (* h3 h3) h4 h5 h6 j2) (* 96 h1 (* h3 h3) h4 h5 h6) (* 7 h1 
(* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 82 h1 (* h3 h3) h4 (* h6 h6) (* j2
 j2 j2 j2)) (* 293 h1 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 402 h1 (* h3 h3) 
h4 (* h6 h6) (* j2 j2)) (* 224 h1 (* h3 h3) h4 (* h6 h6) j2) (* 40 h1 (* h3 h3) 
h4 (* h6 h6)) (* 18 h1 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 86 h1 (* h3
 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 149 h1 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2)
) (* 113 h1 (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 36 h1 (* h3 h3) (* h5 h5 h5) j2
) (* 4 h1 (* h3 h3) (* h5 h5 h5)) (* 8 h1 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 113 h1 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 437 h1 (* h3 h3)
 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 751 h1 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2)) 
(* 626 h1 (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 239 h1 (* h3 h3) (* h5 h5) h6 j2)
 (* 32 h1 (* h3 h3) (* h5 h5) h6) (* 11 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 99 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 404 h1 (* h3 h3)
 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 795 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) 
(* 763 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 340 h1 (* h3 h3) h5 (* h6 h6) j2)
 (* 56 h1 (* h3 h3) h5 (* h6 h6)) (* 2 h1 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 20 h1 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 82 h1 (* h3 h3) 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 188 h1 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 
204 h1 (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 96 h1 (* h3 h3) (* h6 h6 h6) j2) (* 
16 h1 (* h3 h3) (* h6 h6 h6)) (* 4 h1 h3 (* h4 h4 h4) h5 (* j2 j2 j2)) (* 17 h1 
h3 (* h4 h4 h4) h5 (* j2 j2)) (* 21 h1 h3 (* h4 h4 h4) h5 j2) (* 8 h1 h3 (* h4 
h4 h4) h5) (* 3 h1 h3 (* h4 h4 h4) h6 (* j2 j2 j2)) (* 13 h1 h3 (* h4 h4 h4) h6 
(* j2 j2)) (* 10 h1 h3 (* h4 h4 h4) h6 j2) (* 6 h1 h3 (* h4 h4) (* h5 h5) (* j2 
j2 j2 j2)) (* 49 h1 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 107 h1 h3 (* h4 h4) 
(* h5 h5) (* j2 j2)) (* 84 h1 h3 (* h4 h4) (* h5 h5) j2) (* 20 h1 h3 (* h4 h4) 
(* h5 h5)) (* 15 h1 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 98 h1 h3 (* h4 h4) h5
 h6 (* j2 j2 j2)) (* 189 h1 h3 (* h4 h4) h5 h6 (* j2 j2)) (* 142 h1 h3 (* h4 h4)
 h5 h6 j2) (* 32 h1 h3 (* h4 h4) h5 h6) (* 6 h1 h3 (* h4 h4) (* h6 h6) (* j2 j2 
j2 j2)) (* 35 h1 h3 (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 67 h1 h3 (* h4 h4) (* 
h6 h6) (* j2 j2)) (* 30 h1 h3 (* h4 h4) (* h6 h6) j2) (* 20 h1 h3 h4 (* h5 h5 h5
) (* j2 j2 j2 j2)) (* 76 h1 h3 h4 (* h5 h5 h5) (* j2 j2 j2)) (* 98 h1 h3 h4 (* 
h5 h5 h5) (* j2 j2)) (* 50 h1 h3 h4 (* h5 h5 h5) j2) (* 8 h1 h3 h4 (* h5 h5 h5))
 (* 12 h1 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 114 h1 h3 h4 (* h5 h5) h6 
(* j2 j2 j2 j2)) (* 334 h1 h3 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 429 h1 h3 h4 (* 
h5 h5) h6 (* j2 j2)) (* 245 h1 h3 h4 (* h5 h5) h6 j2) (* 48 h1 h3 h4 (* h5 h5) 
h6) (* 13 h1 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 108 h1 h3 h4 h5 (* h6 h6)
 (* j2 j2 j2 j2)) (* 301 h1 h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 375 h1 h3 h4 h5 
(* h6 h6) (* j2 j2)) (* 209 h1 h3 h4 h5 (* h6 h6) j2) (* 40 h1 h3 h4 h5 (* h6 h6
)) (* 2 h1 h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 18 h1 h3 h4 (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 56 h1 h3 h4 (* h6 h6 h6) (* j2 j2 j2)) (* 60 h1 h3 h4 (* h6 
h6 h6) (* j2 j2)) (* 20 h1 h3 h4 (* h6 h6 h6) j2) (* 20 h1 h3 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 95 h1 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 172 h1 h3 
(* h5 h5 h5) h6 (* j2 j2 j2)) (* 147 h1 h3 (* h5 h5 h5) h6 (* j2 j2)) (* 58 h1 
h3 (* h5 h5 h5) h6 j2) (* 8 h1 h3 (* h5 h5 h5) h6) (* 4 h1 h3 (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 56 h1 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
216 h1 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 385 h1 h3 (* h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 354 h1 h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 161 h1 h3 (* h5 h5)
 (* h6 h6) j2) (* 28 h1 h3 (* h5 h5) (* h6 h6)) (* 3 h1 h3 h5 (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 25 h1 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 97 h1 h3 h5
 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 189 h1 h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 188
 h1 h3 h5 (* h6 h6 h6) (* j2 j2)) (* 90 h1 h3 h5 (* h6 h6 h6) j2) (* 16 h1 h3 h5
 (* h6 h6 h6)) (* 3 h1 (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 5 h1 (* h4 h4 h4) 
(* h5 h5) j2) (* 2 h1 (* h4 h4 h4) (* h5 h5)) (* 2 h1 (* h4 h4 h4) h5 h6 (* j2 
j2 j2)) (* 6 h1 (* h4 h4 h4) h5 h6 (* j2 j2)) (* 4 h1 (* h4 h4 h4) h5 h6 j2) (* 
h1 (* h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* 2 h1 (* h4 h4 h4) (* h6 h6) (* j2 j2)
) (* 3 h1 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 8 h1 (* h4 h4) (* h5 h5 h5) 
(* j2 j2)) (* 7 h1 (* h4 h4) (* h5 h5 h5) j2) (* 2 h1 (* h4 h4) (* h5 h5 h5)) 
(* 3 h1 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 21 h1 (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2)) (* 43 h1 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 33 h1 (* h4 h4) (* 
h5 h5) h6 j2) (* 8 h1 (* h4 h4) (* h5 h5) h6) (* 4 h1 (* h4 h4) h5 (* h6 h6) (* 
j2 j2 j2 j2)) (* 21 h1 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 29 h1 (* h4 h4) 
h5 (* h6 h6) (* j2 j2)) (* 12 h1 (* h4 h4) h5 (* h6 h6) j2) (* h1 (* h4 h4) (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 3 h1 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* 2 h1 
(* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 10 h1 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 36 h1 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 48 h1 h4 (* h5 h5 h5) h6 (* j2 j2))
 (* 28 h1 h4 (* h5 h5 h5) h6 j2) (* 6 h1 h4 (* h5 h5 h5) h6) (* 3 h1 h4 (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 25 h1 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2))
 (* 70 h1 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 87 h1 h4 (* h5 h5) (* h6 h6) 
(* j2 j2)) (* 49 h1 h4 (* h5 h5) (* h6 h6) j2) (* 10 h1 h4 (* h5 h5) (* h6 h6)) 
(* 2 h1 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 13 h1 h4 h5 (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 28 h1 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 25 h1 h4 h5 (* h6 h6 h6
) (* j2 j2)) (* 8 h1 h4 h5 (* h6 h6 h6) j2) (* 5 h1 (* h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2)) (* 24 h1 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 46 h1 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 44 h1 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 21 
h1 (* h5 h5 h5) (* h6 h6) j2) (* 4 h1 (* h5 h5 h5) (* h6 h6)) (* 5 h1 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 24 h1 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)
) (* 46 h1 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 44 h1 (* h5 h5) (* h6 h6 h6) 
(* j2 j2)) (* 21 h1 (* h5 h5) (* h6 h6 h6) j2) (* 4 h1 (* h5 h5) (* h6 h6 h6)) 
(* (* h2 h2 h2) (* h3 h3) h4 (* j2 j2 j2 j2 j2)) (* 5 (* h2 h2 h2) (* h3 h3) h4 
(* j2 j2 j2 j2)) (* 10 (* h2 h2 h2) (* h3 h3) h4 (* j2 j2 j2)) (* 10 (* h2 h2 h2
) (* h3 h3) h4 (* j2 j2)) (* 5 (* h2 h2 h2) (* h3 h3) h4 j2) (* (* h2 h2 h2) (* 
h3 h3) h4) (* (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 5 (* h2 h2 h2)
 (* h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 10 (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2
)) (* 10 (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2)) (* 5 (* h2 h2 h2) (* h3 h3) h5 
(* j2 j2)) (* (* h2 h2 h2) (* h3 h3) h5 j2) (* 3 (* h2 h2 h2) (* h3 h3) h6 (* j2
 j2 j2 j2 j2)) (* 13 (* h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2)) (* 22 (* h2 h2 
h2) (* h3 h3) h6 (* j2 j2 j2)) (* 18 (* h2 h2 h2) (* h3 h3) h6 (* j2 j2)) (* 7 
(* h2 h2 h2) (* h3 h3) h6 j2) (* (* h2 h2 h2) (* h3 h3) h6) (* (* h2 h2 h2) h3 
(* h4 h4) (* j2 j2 j2 j2)) (* 4 (* h2 h2 h2) h3 (* h4 h4) (* j2 j2 j2)) (* 6 (* 
h2 h2 h2) h3 (* h4 h4) (* j2 j2)) (* 4 (* h2 h2 h2) h3 (* h4 h4) j2) (* (* h2 h2
 h2) h3 (* h4 h4)) (* 2 (* h2 h2 h2) h3 h4 h5 (* j2 j2 j2 j2 j2)) (* 10 (* h2 h2
 h2) h3 h4 h5 (* j2 j2 j2 j2)) (* 20 (* h2 h2 h2) h3 h4 h5 (* j2 j2 j2)) (* 20 
(* h2 h2 h2) h3 h4 h5 (* j2 j2)) (* 10 (* h2 h2 h2) h3 h4 h5 j2) (* 2 (* h2 h2 
h2) h3 h4 h5) (* 2 (* h2 h2 h2) h3 h4 h6 (* j2 j2 j2 j2 j2)) (* 10 (* h2 h2 h2) 
h3 h4 h6 (* j2 j2 j2 j2)) (* 20 (* h2 h2 h2) h3 h4 h6 (* j2 j2 j2)) (* 20 (* h2 
h2 h2) h3 h4 h6 (* j2 j2)) (* 10 (* h2 h2 h2) h3 h4 h6 j2) (* 2 (* h2 h2 h2) h3 
h4 h6) (* (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 5 (* h2 h2 h2) h3 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 10 (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2)) 
(* 10 (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2)) (* 5 (* h2 h2 h2) h3 (* h5 h5) (* 
j2 j2)) (* (* h2 h2 h2) h3 (* h5 h5) j2) (* 2 (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 
j2 j2 j2)) (* 13 (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 34 (* h2 h2 h2) h3
 h5 h6 (* j2 j2 j2 j2)) (* 46 (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2)) (* 34 (* h2 h2
 h2) h3 h5 h6 (* j2 j2)) (* 13 (* h2 h2 h2) h3 h5 h6 j2) (* 2 (* h2 h2 h2) h3 h5
 h6) (* 3 (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 13 (* h2 h2 h2) h3 
(* h6 h6) (* j2 j2 j2 j2)) (* 22 (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2)) (* 18 
(* h2 h2 h2) h3 (* h6 h6) (* j2 j2)) (* 7 (* h2 h2 h2) h3 (* h6 h6) j2) (* (* h2
 h2 h2) h3 (* h6 h6)) (* (* h2 h2 h2) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 4 (* h2 
h2 h2) (* h4 h4) h5 (* j2 j2 j2)) (* 6 (* h2 h2 h2) (* h4 h4) h5 (* j2 j2)) (* 4
 (* h2 h2 h2) (* h4 h4) h5 j2) (* (* h2 h2 h2) (* h4 h4) h5) (* (* h2 h2 h2) (* 
h4 h4) h6 (* j2 j2 j2 j2)) (* 3 (* h2 h2 h2) (* h4 h4) h6 (* j2 j2 j2)) (* 3 (* 
h2 h2 h2) (* h4 h4) h6 (* j2 j2)) (* (* h2 h2 h2) (* h4 h4) h6 j2) (* (* h2 h2 
h2) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 5 (* h2 h2 h2) h4 (* h5 h5) (* j2 j2 j2 
j2)) (* 10 (* h2 h2 h2) h4 (* h5 h5) (* j2 j2 j2)) (* 10 (* h2 h2 h2) h4 (* h5 
h5) (* j2 j2)) (* 5 (* h2 h2 h2) h4 (* h5 h5) j2) (* (* h2 h2 h2) h4 (* h5 h5)) 
(* 2 (* h2 h2 h2) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 10 (* h2 h2 h2) h4 h5 h6 (* j2
 j2 j2 j2)) (* 20 (* h2 h2 h2) h4 h5 h6 (* j2 j2 j2)) (* 20 (* h2 h2 h2) h4 h5 
h6 (* j2 j2)) (* 10 (* h2 h2 h2) h4 h5 h6 j2) (* 2 (* h2 h2 h2) h4 h5 h6) (* (* 
h2 h2 h2) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4 (* h2 h2 h2) h4 (* h6 h6) (* j2 
j2 j2 j2)) (* 6 (* h2 h2 h2) h4 (* h6 h6) (* j2 j2 j2)) (* 4 (* h2 h2 h2) h4 (* 
h6 h6) (* j2 j2)) (* (* h2 h2 h2) h4 (* h6 h6) j2) (* (* h2 h2 h2) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 6 (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 15 
(* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 20 (* h2 h2 h2) (* h5 h5) h6 (* j2
 j2 j2)) (* 15 (* h2 h2 h2) (* h5 h5) h6 (* j2 j2)) (* 6 (* h2 h2 h2) (* h5 h5) 
h6 j2) (* (* h2 h2 h2) (* h5 h5) h6) (* (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 6 (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 15 (* h2 h2 h2) 
h5 (* h6 h6) (* j2 j2 j2 j2)) (* 20 (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2)) (* 
15 (* h2 h2 h2) h5 (* h6 h6) (* j2 j2)) (* 6 (* h2 h2 h2) h5 (* h6 h6) j2) (* 
(* h2 h2 h2) h5 (* h6 h6)) (* 2 (* h2 h2) (* h3 h3 h3) h4 (* j2 j2 j2 j2 j2)) 
(* 10 (* h2 h2) (* h3 h3 h3) h4 (* j2 j2 j2 j2)) (* 20 (* h2 h2) (* h3 h3 h3) h4
 (* j2 j2 j2)) (* 20 (* h2 h2) (* h3 h3 h3) h4 (* j2 j2)) (* 10 (* h2 h2) (* h3 
h3 h3) h4 j2) (* 2 (* h2 h2) (* h3 h3 h3) h4) (* 2 (* h2 h2) (* h3 h3 h3) h5 (* 
j2 j2 j2 j2 j2 j2)) (* 10 (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 20 
(* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 20 (* h2 h2) (* h3 h3 h3) h5 (* j2
 j2 j2)) (* 10 (* h2 h2) (* h3 h3 h3) h5 (* j2 j2)) (* 2 (* h2 h2) (* h3 h3 h3) 
h5 j2) (* 6 (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 26 (* h2 h2) (* h3 
h3 h3) h6 (* j2 j2 j2 j2)) (* 44 (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2)) (* 36 
(* h2 h2) (* h3 h3 h3) h6 (* j2 j2)) (* 14 (* h2 h2) (* h3 h3 h3) h6 j2) (* 2 
(* h2 h2) (* h3 h3 h3) h6) (* 4 (* h2 h2) (* h3 h3) (* h4 h4) (* j2 j2 j2 j2)) 
(* 16 (* h2 h2) (* h3 h3) (* h4 h4) (* j2 j2 j2)) (* 24 (* h2 h2) (* h3 h3) (* 
h4 h4) (* j2 j2)) (* 16 (* h2 h2) (* h3 h3) (* h4 h4) j2) (* 4 (* h2 h2) (* h3 
h3) (* h4 h4)) (* 8 (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 41 (* h2 h2
) (* h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 82 (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2))
 (* 80 (* h2 h2) (* h3 h3) h4 h5 (* j2 j2)) (* 38 (* h2 h2) (* h3 h3) h4 h5 j2) 
(* 7 (* h2 h2) (* h3 h3) h4 h5) (* 7 (* h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2
)) (* 38 (* h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 80 (* h2 h2) (* h3 h3) h4
 h6 (* j2 j2 j2)) (* 82 (* h2 h2) (* h3 h3) h4 h6 (* j2 j2)) (* 41 (* h2 h2) (* 
h3 h3) h4 h6 j2) (* 8 (* h2 h2) (* h3 h3) h4 h6) (* 4 (* h2 h2) (* h3 h3) (* h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 21 (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2
)) (* 43 (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 43 (* h2 h2) (* h3 h3
) (* h5 h5) (* j2 j2 j2)) (* 21 (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2)) (* 4 
(* h2 h2) (* h3 h3) (* h5 h5) j2) (* 7 (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 
j2 j2)) (* 48 (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 132 (* h2 h2) (* 
h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 183 (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2)) (* 
134 (* h2 h2) (* h3 h3) h5 h6 (* j2 j2)) (* 49 (* h2 h2) (* h3 h3) h5 h6 j2) (* 
7 (* h2 h2) (* h3 h3) h5 h6) (* 12 (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 52 (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 88 (* h2 h2) (* h3 
h3) (* h6 h6) (* j2 j2 j2)) (* 72 (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2)) (* 28
 (* h2 h2) (* h3 h3) (* h6 h6) j2) (* 4 (* h2 h2) (* h3 h3) (* h6 h6)) (* (* h2 
h2) h3 (* h4 h4 h4) (* j2 j2 j2)) (* 3 (* h2 h2) h3 (* h4 h4 h4) (* j2 j2)) (* 3
 (* h2 h2) h3 (* h4 h4 h4) j2) (* (* h2 h2) h3 (* h4 h4 h4)) (* 7 (* h2 h2) h3 
(* h4 h4) h5 (* j2 j2 j2 j2)) (* 29 (* h2 h2) h3 (* h4 h4) h5 (* j2 j2 j2)) (* 
44 (* h2 h2) h3 (* h4 h4) h5 (* j2 j2)) (* 29 (* h2 h2) h3 (* h4 h4) h5 j2) (* 7
 (* h2 h2) h3 (* h4 h4) h5) (* 7 (* h2 h2) h3 (* h4 h4) h6 (* j2 j2 j2 j2)) (* 
24 (* h2 h2) h3 (* h4 h4) h6 (* j2 j2 j2)) (* 30 (* h2 h2) h3 (* h4 h4) h6 (* j2
 j2)) (* 16 (* h2 h2) h3 (* h4 h4) h6 j2) (* 3 (* h2 h2) h3 (* h4 h4) h6) (* 7 
(* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 36 (* h2 h2) h3 h4 (* h5 h5) 
(* j2 j2 j2 j2)) (* 72 (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2)) (* 70 (* h2 h2) 
h3 h4 (* h5 h5) (* j2 j2)) (* 33 (* h2 h2) h3 h4 (* h5 h5) j2) (* 6 (* h2 h2) h3
 h4 (* h5 h5)) (* 14 (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 73 (* h2 h2) 
h3 h4 h5 h6 (* j2 j2 j2 j2)) (* 149 (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2)) (* 149 
(* h2 h2) h3 h4 h5 h6 (* j2 j2)) (* 73 (* h2 h2) h3 h4 h5 h6 j2) (* 14 (* h2 h2)
 h3 h4 h5 h6) (* 6 (* h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 29 (* h2 h2)
 h3 h4 (* h6 h6) (* j2 j2 j2 j2)) (* 54 (* h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2)) 
(* 48 (* h2 h2) h3 h4 (* h6 h6) (* j2 j2)) (* 20 (* h2 h2) h3 h4 (* h6 h6) j2) 
(* 3 (* h2 h2) h3 h4 (* h6 h6)) (* (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 5 (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 10 (* h2 h2) h3 (* h5
 h5 h5) (* j2 j2 j2 j2)) (* 10 (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 5 (* 
h2 h2) h3 (* h5 h5 h5) (* j2 j2)) (* (* h2 h2) h3 (* h5 h5 h5) j2) (* 7 (* h2 h2
) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 44 (* h2 h2) h3 (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 112 (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 148 (* h2 h2)
 h3 (* h5 h5) h6 (* j2 j2 j2)) (* 107 (* h2 h2) h3 (* h5 h5) h6 (* j2 j2)) (* 40
 (* h2 h2) h3 (* h5 h5) h6 j2) (* 6 (* h2 h2) h3 (* h5 h5) h6) (* 6 (* h2 h2) h3
 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 41 (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2
 j2 j2)) (* 111 (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 154 (* h2 h2) h3 
h5 (* h6 h6) (* j2 j2 j2)) (* 116 (* h2 h2) h3 h5 (* h6 h6) (* j2 j2)) (* 45 (* 
h2 h2) h3 h5 (* h6 h6) j2) (* 7 (* h2 h2) h3 h5 (* h6 h6)) (* 3 (* h2 h2) h3 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 13 (* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 22 (* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 18 (* h2 h2) h3 (* h6 h6 h6) 
(* j2 j2)) (* 7 (* h2 h2) h3 (* h6 h6 h6) j2) (* (* h2 h2) h3 (* h6 h6 h6)) (* 
(* h2 h2) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 3 (* h2 h2) (* h4 h4 h4) h5 (* j2 j2)
) (* 3 (* h2 h2) (* h4 h4 h4) h5 j2) (* (* h2 h2) (* h4 h4 h4) h5) (* (* h2 h2) 
(* h4 h4 h4) h6 (* j2 j2 j2)) (* 2 (* h2 h2) (* h4 h4 h4) h6 (* j2 j2)) (* (* h2
 h2) (* h4 h4 h4) h6 j2) (* 2 (* h2 h2) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 
8 (* h2 h2) (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 12 (* h2 h2) (* h4 h4) (* h5 h5
) (* j2 j2)) (* 8 (* h2 h2) (* h4 h4) (* h5 h5) j2) (* 2 (* h2 h2) (* h4 h4) (* 
h5 h5)) (* 4 (* h2 h2) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 15 (* h2 h2) (* h4 h4
) h5 h6 (* j2 j2 j2)) (* 21 (* h2 h2) (* h4 h4) h5 h6 (* j2 j2)) (* 13 (* h2 h2)
 (* h4 h4) h5 h6 j2) (* 3 (* h2 h2) (* h4 h4) h5 h6) (* 2 (* h2 h2) (* h4 h4) 
(* h6 h6) (* j2 j2 j2 j2)) (* 6 (* h2 h2) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 6
 (* h2 h2) (* h4 h4) (* h6 h6) (* j2 j2)) (* 2 (* h2 h2) (* h4 h4) (* h6 h6) j2)
 (* (* h2 h2) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 5 (* h2 h2) h4 (* h5 h5 h5)
 (* j2 j2 j2 j2)) (* 10 (* h2 h2) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 10 (* h2 h2) 
h4 (* h5 h5 h5) (* j2 j2)) (* 5 (* h2 h2) h4 (* h5 h5 h5) j2) (* (* h2 h2) h4 
(* h5 h5 h5)) (* 4 (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 20 (* h2 h2)
 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 40 (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2)) 
(* 40 (* h2 h2) h4 (* h5 h5) h6 (* j2 j2)) (* 20 (* h2 h2) h4 (* h5 h5) h6 j2) 
(* 4 (* h2 h2) h4 (* h5 h5) h6) (* 4 (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2
)) (* 19 (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 36 (* h2 h2) h4 h5 (* h6 
h6) (* j2 j2 j2)) (* 34 (* h2 h2) h4 h5 (* h6 h6) (* j2 j2)) (* 16 (* h2 h2) h4 
h5 (* h6 h6) j2) (* 3 (* h2 h2) h4 h5 (* h6 h6)) (* (* h2 h2) h4 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 4 (* h2 h2) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 6 (* h2 
h2) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 4 (* h2 h2) h4 (* h6 h6 h6) (* j2 j2)) (* 
(* h2 h2) h4 (* h6 h6 h6) j2) (* (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)
) (* 6 (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 15 (* h2 h2) (* h5 h5 h5
) h6 (* j2 j2 j2 j2)) (* 20 (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 15 (* h2 
h2) (* h5 h5 h5) h6 (* j2 j2)) (* 6 (* h2 h2) (* h5 h5 h5) h6 j2) (* (* h2 h2) 
(* h5 h5 h5) h6) (* 2 (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12
 (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 30 (* h2 h2) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 40 (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 30 
(* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2)) (* 12 (* h2 h2) (* h5 h5) (* h6 h6) j2)
 (* 2 (* h2 h2) (* h5 h5) (* h6 h6)) (* (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 6 (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 15 (* h2 h2) h5 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 20 (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 
15 (* h2 h2) h5 (* h6 h6 h6) (* j2 j2)) (* 6 (* h2 h2) h5 (* h6 h6 h6) j2) (* 
(* h2 h2) h5 (* h6 h6 h6)) (* 4 h2 (* h3 h3 h3) (* h4 h4) (* j2 j2 j2 j2)) (* 16
 h2 (* h3 h3 h3) (* h4 h4) (* j2 j2 j2)) (* 24 h2 (* h3 h3 h3) (* h4 h4) (* j2 
j2)) (* 16 h2 (* h3 h3 h3) (* h4 h4) j2) (* 4 h2 (* h3 h3 h3) (* h4 h4)) (* 8 h2
 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 40 h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2 
j2)) (* 76 h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 68 h2 (* h3 h3 h3) h4 h5 (* j2
 j2)) (* 28 h2 (* h3 h3 h3) h4 h5 j2) (* 4 h2 (* h3 h3 h3) h4 h5) (* 4 h2 (* h3 
h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 32 h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) 
(* 80 h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 88 h2 (* h3 h3 h3) h4 h6 (* j2 j2))
 (* 44 h2 (* h3 h3 h3) h4 h6 j2) (* 8 h2 (* h3 h3 h3) h4 h6) (* 4 h2 (* h3 h3 h3
) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 20 h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 
j2 j2)) (* 38 h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 34 h2 (* h3 h3 h3) 
(* h5 h5) (* j2 j2 j2)) (* 14 h2 (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 2 h2 (* h3
 h3 h3) (* h5 h5) j2) (* 4 h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 40 h2
 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 122 h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2
 j2)) (* 166 h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 110 h2 (* h3 h3 h3) h5 h6 
(* j2 j2)) (* 34 h2 (* h3 h3 h3) h5 h6 j2) (* 4 h2 (* h3 h3 h3) h5 h6) (* 6 h2 
(* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 44 h2 (* h3 h3 h3) (* h6 h6) (* j2
 j2 j2 j2)) (* 92 h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 80 h2 (* h3 h3 h3) 
(* h6 h6) (* j2 j2)) (* 30 h2 (* h3 h3 h3) (* h6 h6) j2) (* 4 h2 (* h3 h3 h3) 
(* h6 h6)) (* 2 h2 (* h3 h3) (* h4 h4 h4) (* j2 j2 j2)) (* 6 h2 (* h3 h3) (* h4 
h4 h4) (* j2 j2)) (* 6 h2 (* h3 h3) (* h4 h4 h4) j2) (* 2 h2 (* h3 h3) (* h4 h4 
h4)) (* 14 h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 58 h2 (* h3 h3) (* h4 
h4) h5 (* j2 j2 j2)) (* 86 h2 (* h3 h3) (* h4 h4) h5 (* j2 j2)) (* 54 h2 (* h3 
h3) (* h4 h4) h5 j2) (* 12 h2 (* h3 h3) (* h4 h4) h5) (* 12 h2 (* h3 h3) (* h4 
h4) h6 (* j2 j2 j2 j2)) (* 46 h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 62 h2 
(* h3 h3) (* h4 h4) h6 (* j2 j2)) (* 34 h2 (* h3 h3) (* h4 h4) h6 j2) (* 6 h2 
(* h3 h3) (* h4 h4) h6) (* 14 h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
72 h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 139 h2 (* h3 h3) h4 (* h5 h5) 
(* j2 j2 j2)) (* 124 h2 (* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 50 h2 (* h3 h3) h4 
(* h5 h5) j2) (* 7 h2 (* h3 h3) h4 (* h5 h5)) (* 24 h2 (* h3 h3) h4 h5 h6 (* j2 
j2 j2 j2 j2)) (* 138 h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 297 h2 (* h3 h3) 
h4 h5 h6 (* j2 j2 j2)) (* 298 h2 (* h3 h3) h4 h5 h6 (* j2 j2)) (* 139 h2 (* h3 
h3) h4 h5 h6 j2) (* 24 h2 (* h3 h3) h4 h5 h6) (* 7 h2 (* h3 h3) h4 (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 50 h2 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 110 h2 (* 
h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 104 h2 (* h3 h3) h4 (* h6 h6) (* j2 j2)) 
(* 43 h2 (* h3 h3) h4 (* h6 h6) j2) (* 6 h2 (* h3 h3) h4 (* h6 h6)) (* 2 h2 (* 
h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 10 h2 (* h3 h3) (* h5 h5 h5) (* j2
 j2 j2 j2 j2)) (* 19 h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 17 h2 (* h3 
h3) (* h5 h5 h5) (* j2 j2 j2)) (* 7 h2 (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* h2 
(* h3 h3) (* h5 h5 h5) j2) (* 12 h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)
) (* 80 h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 209 h2 (* h3 h3) (* h5 
h5) h6 (* j2 j2 j2 j2)) (* 270 h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 180 h2
 (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 58 h2 (* h3 h3) (* h5 h5) h6 j2) (* 7 h2 
(* h3 h3) (* h5 h5) h6) (* 7 h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 66 h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 207 h2 (* h3 h3) h5 (* h6
 h6) (* j2 j2 j2 j2)) (* 305 h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 230 h2 
(* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 85 h2 (* h3 h3) h5 (* h6 h6) j2) (* 12 h2 
(* h3 h3) h5 (* h6 h6)) (* 3 h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 22
 h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 46 h2 (* h3 h3) (* h6 h6 h6) (* 
j2 j2 j2)) (* 40 h2 (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 15 h2 (* h3 h3) (* h6 
h6 h6) j2) (* 2 h2 (* h3 h3) (* h6 h6 h6)) (* 4 h2 h3 (* h4 h4 h4) h5 (* j2 j2 
j2)) (* 13 h2 h3 (* h4 h4 h4) h5 (* j2 j2)) (* 13 h2 h3 (* h4 h4 h4) h5 j2) (* 4
 h2 h3 (* h4 h4 h4) h5) (* 4 h2 h3 (* h4 h4 h4) h6 (* j2 j2 j2)) (* 8 h2 h3 (* 
h4 h4 h4) h6 (* j2 j2)) (* 4 h2 h3 (* h4 h4 h4) h6 j2) (* 8 h2 h3 (* h4 h4) (* 
h5 h5) (* j2 j2 j2 j2)) (* 33 h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 49 h2 
h3 (* h4 h4) (* h5 h5) (* j2 j2)) (* 31 h2 h3 (* h4 h4) (* h5 h5) j2) (* 7 h2 h3
 (* h4 h4) (* h5 h5)) (* 16 h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 62 h2 h3 
(* h4 h4) h5 h6 (* j2 j2 j2)) (* 90 h2 h3 (* h4 h4) h5 h6 (* j2 j2)) (* 56 h2 h3
 (* h4 h4) h5 h6 j2) (* 12 h2 h3 (* h4 h4) h5 h6) (* 7 h2 h3 (* h4 h4) (* h6 h6)
 (* j2 j2 j2 j2)) (* 24 h2 h3 (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 25 h2 h3 (* 
h4 h4) (* h6 h6) (* j2 j2)) (* 8 h2 h3 (* h4 h4) (* h6 h6) j2) (* 4 h2 h3 h4 (* 
h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 20 h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 38
 h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2)) (* 34 h2 h3 h4 (* h5 h5 h5) (* j2 j2)) (* 
14 h2 h3 h4 (* h5 h5 h5) j2) (* 2 h2 h3 h4 (* h5 h5 h5)) (* 16 h2 h3 h4 (* h5 h5
) h6 (* j2 j2 j2 j2 j2)) (* 84 h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 170 h2 
h3 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 166 h2 h3 h4 (* h5 h5) h6 (* j2 j2)) (* 78 
h2 h3 h4 (* h5 h5) h6 j2) (* 14 h2 h3 h4 (* h5 h5) h6) (* 14 h2 h3 h4 h5 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 75 h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 154 h2 
h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 151 h2 h3 h4 h5 (* h6 h6) (* j2 j2)) (* 70 
h2 h3 h4 h5 (* h6 h6) j2) (* 12 h2 h3 h4 h5 (* h6 h6)) (* 2 h2 h3 h4 (* h6 h6 h6
) (* j2 j2 j2 j2 j2)) (* 14 h2 h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 26 h2 h3 
h4 (* h6 h6 h6) (* j2 j2 j2)) (* 18 h2 h3 h4 (* h6 h6 h6) (* j2 j2)) (* 4 h2 h3 
h4 (* h6 h6 h6) j2) (* 4 h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 24 h2 
h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 58 h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 72 h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 48 h2 h3 (* h5 h5 h5) h6 (* j2
 j2)) (* 16 h2 h3 (* h5 h5 h5) h6 j2) (* 2 h2 h3 (* h5 h5 h5) h6) (* 7 h2 h3 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 47 h2 h3 (* h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2)) (* 125 h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 170 h2 h3 (* h5
 h5) (* h6 h6) (* j2 j2 j2)) (* 125 h2 h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 47 
h2 h3 (* h5 h5) (* h6 h6) j2) (* 7 h2 h3 (* h5 h5) (* h6 h6)) (* 2 h2 h3 h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 19 h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 60 h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 90 h2 h3 h5 (* h6 h6 h6) (* j2 
j2 j2)) (* 70 h2 h3 h5 (* h6 h6 h6) (* j2 j2)) (* 27 h2 h3 h5 (* h6 h6 h6) j2) 
(* 4 h2 h3 h5 (* h6 h6 h6)) (* h2 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 3 h2 
(* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 3 h2 (* h4 h4 h4) (* h5 h5) j2) (* h2 (* h4
 h4 h4) (* h5 h5)) (* 2 h2 (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 4 h2 (* h4 h4 h4)
 h5 h6 (* j2 j2)) (* 2 h2 (* h4 h4 h4) h5 h6 j2) (* h2 (* h4 h4 h4) (* h6 h6) 
(* j2 j2 j2)) (* h2 (* h4 h4 h4) (* h6 h6) (* j2 j2)) (* h2 (* h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2)) (* 4 h2 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 6 h2 (* h4 
h4) (* h5 h5 h5) (* j2 j2)) (* 4 h2 (* h4 h4) (* h5 h5 h5) j2) (* h2 (* h4 h4) 
(* h5 h5 h5)) (* 4 h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 15 h2 (* h4 h4)
 (* h5 h5) h6 (* j2 j2 j2)) (* 21 h2 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 13 h2 
(* h4 h4) (* h5 h5) h6 j2) (* 3 h2 (* h4 h4) (* h5 h5) h6) (* 4 h2 (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2)) (* 12 h2 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 12 
h2 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 4 h2 (* h4 h4) h5 (* h6 h6) j2) (* h2 
(* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2 h2 (* h4 h4) (* h6 h6 h6) (* j2 j2 
j2)) (* h2 (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 2 h2 h4 (* h5 h5 h5) h6 (* j2 j2
 j2 j2 j2)) (* 10 h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 20 h2 h4 (* h5 h5 h5
) h6 (* j2 j2 j2)) (* 20 h2 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 10 h2 h4 (* h5 h5 
h5) h6 j2) (* 2 h2 h4 (* h5 h5 h5) h6) (* 4 h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 19 h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 36 h2 h4 (* h5 h5
) (* h6 h6) (* j2 j2 j2)) (* 34 h2 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 16 h2 h4
 (* h5 h5) (* h6 h6) j2) (* 3 h2 h4 (* h5 h5) (* h6 h6)) (* 2 h2 h4 h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 8 h2 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 12 h2 h4 
h5 (* h6 h6 h6) (* j2 j2 j2)) (* 8 h2 h4 h5 (* h6 h6 h6) (* j2 j2)) (* 2 h2 h4 
h5 (* h6 h6 h6) j2) (* h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 h2 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 15 h2 (* h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2)) (* 20 h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 15 h2 (* h5 h5 h5) 
(* h6 h6) (* j2 j2)) (* 6 h2 (* h5 h5 h5) (* h6 h6) j2) (* h2 (* h5 h5 h5) (* h6
 h6)) (* h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 h2 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 15 h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 20 h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 15 h2 (* h5 h5) (* h6 h6 h6) 
(* j2 j2)) (* 6 h2 (* h5 h5) (* h6 h6 h6) j2) (* h2 (* h5 h5) (* h6 h6 h6)) (* 8
 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 32 (* h3 h3 h3) (* h4 h4) h5 (* 
j2 j2 j2)) (* 44 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 24 (* h3 h3 h3) (* h4 
h4) h5 j2) (* 4 (* h3 h3 h3) (* h4 h4) h5) (* 4 (* h3 h3 h3) (* h4 h4) h6 (* j2 
j2 j2 j2)) (* 20 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 28 (* h3 h3 h3) (* 
h4 h4) h6 (* j2 j2)) (* 12 (* h3 h3 h3) (* h4 h4) h6 j2) (* 8 (* h3 h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 40 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) 
(* 72 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 56 (* h3 h3 h3) h4 (* h5 h5) 
(* j2 j2)) (* 18 (* h3 h3 h3) h4 (* h5 h5) j2) (* 2 (* h3 h3 h3) h4 (* h5 h5)) 
(* 8 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 64 (* h3 h3 h3) h4 h5 h6 (* j2
 j2 j2 j2)) (* 156 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 152 (* h3 h3 h3) h4 h5
 h6 (* j2 j2)) (* 60 (* h3 h3 h3) h4 h5 h6 j2) (* 8 (* h3 h3 h3) h4 h5 h6) (* 2 
(* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 18 (* h3 h3 h3) h4 (* h6 h6) 
(* j2 j2 j2 j2)) (* 50 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 46 (* h3 h3 h3
) h4 (* h6 h6) (* j2 j2)) (* 12 (* h3 h3 h3) h4 (* h6 h6) j2) (* 4 (* h3 h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 32 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 90 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 116 (* h3 h3 h3) (* 
h5 h5) h6 (* j2 j2 j2)) (* 72 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 20 (* h3 
h3 h3) (* h5 h5) h6 j2) (* 2 (* h3 h3 h3) (* h5 h5) h6) (* 2 (* h3 h3 h3) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 22 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 84 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 136 (* h3 h3 h3) h5 (* h6 
h6) (* j2 j2 j2)) (* 102 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 34 (* h3 h3 h3)
 h5 (* h6 h6) j2) (* 4 (* h3 h3 h3) h5 (* h6 h6)) (* 4 (* h3 h3) (* h4 h4 h4) h5
 (* j2 j2 j2)) (* 12 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 10 (* h3 h3) (* h4 
h4 h4) h5 j2) (* 2 (* h3 h3) (* h4 h4 h4) h5) (* 2 (* h3 h3) (* h4 h4 h4) h6 (* 
j2 j2 j2)) (* 8 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 6 (* h3 h3) (* h4 h4 h4)
 h6 j2) (* 8 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 32 (* h3 h3) (* 
h4 h4) (* h5 h5) (* j2 j2 j2)) (* 44 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) 
(* 24 (* h3 h3) (* h4 h4) (* h5 h5) j2) (* 4 (* h3 h3) (* h4 h4) (* h5 h5)) (* 
14 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 60 (* h3 h3) (* h4 h4) h5 h6 
(* j2 j2 j2)) (* 88 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 48 (* h3 h3) (* h4 
h4) h5 h6 j2) (* 6 (* h3 h3) (* h4 h4) h5 h6) (* 4 (* h3 h3) (* h4 h4) (* h6 h6)
 (* j2 j2 j2 j2)) (* 20 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 28 (* h3 
h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 12 (* h3 h3) (* h4 h4) (* h6 h6) j2) (* 4 
(* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 20 (* h3 h3) h4 (* h5 h5 h5) 
(* j2 j2 j2 j2)) (* 36 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 28 (* h3 h3) 
h4 (* h5 h5 h5) (* j2 j2)) (* 9 (* h3 h3) h4 (* h5 h5 h5) j2) (* (* h3 h3) h4 
(* h5 h5 h5)) (* 14 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 78 (* h3 h3
) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 159 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)
) (* 145 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 58 (* h3 h3) h4 (* h5 h5) h6 j2
) (* 8 (* h3 h3) h4 (* h5 h5) h6) (* 8 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 63 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 149 (* h3 h3) h4 h5 (* 
h6 h6) (* j2 j2 j2)) (* 143 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 55 (* h3 h3)
 h4 h5 (* h6 h6) j2) (* 6 (* h3 h3) h4 h5 (* h6 h6)) (* (* h3 h3) h4 (* h6 h6 h6
) (* j2 j2 j2 j2 j2)) (* 9 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 25 (* 
h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 23 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2)) 
(* 6 (* h3 h3) h4 (* h6 h6 h6) j2) (* 2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2)) (* 16 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 45 (* h3 h3) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 58 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 
36 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 10 (* h3 h3) (* h5 h5 h5) h6 j2) (* 
(* h3 h3) (* h5 h5 h5) h6) (* 4 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 33 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 98 (* h3 h3) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 138 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2)) (* 98 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 33 (* h3 h3) (* h5 h5) 
(* h6 h6) j2) (* 4 (* h3 h3) (* h5 h5) (* h6 h6)) (* (* h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 11 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 42
 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 68 (* h3 h3) h5 (* h6 h6 h6) (* 
j2 j2 j2)) (* 51 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 17 (* h3 h3) h5 (* h6 
h6 h6) j2) (* 2 (* h3 h3) h5 (* h6 h6 h6)) (* 2 h3 (* h4 h4 h4) (* h5 h5) (* j2 
j2 j2)) (* 6 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 5 h3 (* h4 h4 h4) (* h5 h5)
 j2) (* h3 (* h4 h4 h4) (* h5 h5)) (* 4 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 9
 h3 (* h4 h4 h4) h5 h6 (* j2 j2)) (* 5 h3 (* h4 h4 h4) h5 h6 j2) (* h3 (* h4 h4 
h4) (* h6 h6) (* j2 j2 j2)) (* 3 h3 (* h4 h4 h4) (* h6 h6) (* j2 j2)) (* 2 h3 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 8 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 
j2)) (* 11 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 6 h3 (* h4 h4) (* h5 h5 h5) 
j2) (* h3 (* h4 h4) (* h5 h5 h5)) (* 8 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)
) (* 31 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 43 h3 (* h4 h4) (* h5 h5) h6 
(* j2 j2)) (* 23 h3 (* h4 h4) (* h5 h5) h6 j2) (* 3 h3 (* h4 h4) (* h5 h5) h6) 
(* 7 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 25 h3 (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2)) (* 28 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 10 h3 (* h4 h4) h5 
(* h6 h6) j2) (* h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4 h3 (* h4 h4) 
(* h6 h6 h6) (* j2 j2 j2)) (* 3 h3 (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 4 h3 h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 20 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2))
 (* 38 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 34 h3 h4 (* h5 h5 h5) h6 (* j2 j2)
) (* 14 h3 h4 (* h5 h5 h5) h6 j2) (* 2 h3 h4 (* h5 h5 h5) h6) (* 7 h3 h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 37 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
)) (* 73 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 66 h3 h4 (* h5 h5) (* h6 h6)
 (* j2 j2)) (* 26 h3 h4 (* h5 h5) (* h6 h6) j2) (* 3 h3 h4 (* h5 h5) (* h6 h6)) 
(* 2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 14 h3 h4 h5 (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 27 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 20 h3 h4 h5 (* h6 h6 h6
) (* j2 j2)) (* 5 h3 h4 h5 (* h6 h6 h6) j2) (* h3 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 8 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 23 h3 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 32 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
)) (* 23 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 8 h3 (* h5 h5 h5) (* h6 h6) j2)
 (* h3 (* h5 h5 h5) (* h6 h6)) (* h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
)) (* 8 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 23 h3 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2)) (* 32 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 23 h3 
(* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 8 h3 (* h5 h5) (* h6 h6 h6) j2) (* h3 (* h5
 h5) (* h6 h6 h6)) (* (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 2 (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2)) (* (* h4 h4 h4) (* h5 h5) h6 j2) (* (* h4 h4 h4) h5 (* 
h6 h6) (* j2 j2 j2)) (* (* h4 h4 h4) h5 (* h6 h6) (* j2 j2)) (* (* h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2 j2)) (* 3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 3 (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* (* h4 h4) (* h5 h5 h5) h6 j2) (* 2 (* h4 h4
) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 
j2 j2)) (* 6 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 2 (* h4 h4) (* h5 h5) 
(* h6 h6) j2) (* (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2 (* h4 h4) h5 
(* h6 h6 h6) (* j2 j2 j2)) (* (* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* h4 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2)) (* 6 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 4 h4 (* h5 h5 h5) (* h6 h6)
 (* j2 j2)) (* h4 (* h5 h5 h5) (* h6 h6) j2) (* h4 (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 4 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 6 h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2)) (* 4 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* h4 (* h5
 h5) (* h6 h6 h6) j2)) 0)))
(check-sat)
(exit)
