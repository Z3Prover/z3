(set-option :proof true)
(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun d () String)
(declare-fun e () String)
(declare-fun f () Bool)
(declare-fun g () String)
(declare-fun h () Int)
(declare-fun i () Int)
(declare-fun j () String)
(declare-fun k () Bool)
(declare-fun l () Bool)
(declare-fun m () String)
(declare-fun n () String)
(declare-fun o () String)
(assert (ite k (xor (distinct i h (str.len (str.substr o 2 (str.len j)))))
         (str.in.re (str.substr b 2 0) (str.to.re "."))))
(assert (= l (= "" (str.substr g 10 (str.len m))) (xor (= f l))
         (distinct ""
          (str.substr a 0
           (str.len
            (str.substr c 0
             (str.len
              (str.substr d 0
               (str.len
                (str.substr o
                 (str.len j)
                 (str.len (str.substr e 0 (str.len n)))))))))))))
(assert (distinct f l))
(assert (= a (str.++ n) c d o e))
(check-sat)