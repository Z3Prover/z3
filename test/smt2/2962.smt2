(set-logic QF_UFLIA)
(set-option :model_validate true)
(declare-fun a (Int) Int)
(declare-fun b (Int) Int)
(declare-fun c (Int) Int)
(declare-fun d (Int) Int)
(declare-fun ab (Int) Int)
(declare-fun e () Int)
(declare-fun f () Int)
(declare-fun aa () Int)
(declare-fun g () Int)
(declare-fun h () Int)
(declare-fun i () Int)
(declare-fun j () Int)
(assert
 (let ((k j) (l e) (b f) (m aa) (n (b h)) (o 0) (p (c i)) (q (d e)) (r (d f)) (s (d aa)) (t 0) (u (d j))
       (v (ab e)) (w (b f)) (x (b aa)) (y (ab g)) (z (ab i)) (ac (+ e j)) (ad (+ e f)))
  (and
   (or
    (and
     (or
      (and
       (or
        (and
         (or
          (and
           (or (and (or (= q h) (= r e) (= r aa) (= r g) (distinct r h) (= r j)) (= s i) (distinct s j)) (distinct t i))
           (or (= u f aa) (= u h) (= u i) (= u j))
           (or (= v e) (= v aa) (= v h) (= v i))
           (= w j))
          (and (or (distinct x e f h) (= x i)) (= x j y i)) (distinct y j))
         (or (and (or (= z g) (= z h)) (= z i)) (distinct z j)))
        (distinct e aa))
       (distinct e g))
      (distinct e h) (distinct e i))
     (distinct f g) (distinct f i) (distinct f j) (distinct aa g) (distinct aa h)
     (distinct aa i) (= aa j) (distinct g h) (distinct g i) (distinct g j)
     (distinct h i) (= h j) (distinct i j) (< e 8) (< f 8) (<= 0 aa 8) (< h 5))
    (< i 8))
   (<= 0 j 8) (distinct (a (a (ab (ite (< ac 8) ac e)))) (a (a (ab (ite (< ad 8) ad e))))))))
(check-sat)
