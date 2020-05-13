(declare-fun c (Int) Int)
(declare-fun br (Int) Int)
(declare-fun cn (Int) Int)
(declare-fun cm (Int) Int)
(declare-fun a (Int) Int)
(declare-fun g () Int)
(declare-fun h () Int)
(declare-fun d () Int)
(declare-fun j () Int)
(declare-fun f () Int)
(declare-fun co () Int)
(declare-fun k () Int)
(declare-fun l () Int)
(declare-fun m () Int)
(declare-fun cp () Int)
(assert
(let (
      (n (br co)) (cg (a l)))
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
            (or
             (and
              (or (= (a h) k) (= (a h) l) (= n h))
              (= (a j) f l) (distinct (a co) m) (= (a k) f k))
             (distinct n j) (= cg f) (distinct cg co)
             (= cg k) (= cg l) (= cg m) (= cg cp))
            (= (a cp) cp) (distinct g h)
            (distinct g d)))
          (distinct g l) (distinct h f) (distinct d k) (distinct d l)))
        (distinct d cp) (distinct j f) (distinct j co) (distinct j k)
        (distinct j l) (distinct j m) (= j cp))
       (distinct f m) (distinct f cp))
      (distinct co k) (distinct k cp) (distinct l m) (distinct l cp))
     (> g 1))
    (<= 0 h 11) (< k 1) (<= 0 m)))
  (= (c (c (a (ite (< (- g cp) 11) (- g cp) g))))
   (c (c (a (ite (< (+ g h) 11) (+ g h) g))))))))
;(apply dom-simplify)
(check-sat-using (then dom-simplify smt))