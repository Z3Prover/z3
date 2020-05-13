(declare-fun a (Int) Int)
(declare-fun b (Int) Int)
(declare-fun c (Int) Int)
(declare-fun d (Int) Int)
(declare-fun e (Int) Int)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun h () Int)
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun l () Int)
(declare-fun m () Int)
(declare-fun u () Int)
(assert
 (let ((k j))
  (and
   (or
    (and
     (or
      (and
       (or
        (and
         (or
          (and
           (or
            (and
             (or (and (= (a m) h (a u) u)) (= 0 u))
             (= i (a i)))
            (= h (b i) (b l) i))
           (= i 0))
          (= (c j) u) (= u i))
         (distinct l h)
         (= 0 (d h) l m (f m) i)
         (distinct (f l) (e m) i))
        (= (e j) m j l j)
        (= (e u) i))
       (or (and (or (= 0 j)) (= (g h) i)) (= 0 h)))
      (= l i))
     (distinct h m u))
    (distinct j i))
   (< h 7)
   (<= 7 u 7)
   (<= i (a (a (g (ite (< (+ h l) 7) (+ h l) h))))))))
(check-sat)