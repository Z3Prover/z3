(declare-fun offset () Int)
(declare-fun s1 () String)
(declare-fun s2 () String)
(assert
   (= -1 (str.indexof s1 s2 offset)))
(check-sat)
(reset)

(declare-fun str0 () String)
(declare-fun str1 () String)
(declare-fun str2 () String)
(declare-fun src () String)
(declare-fun dst () String)
(declare-fun s () String)
(declare-const i Int)
(assert
   (= src (str.at (str.replace str0 str1 str2) i)))
(assert
   (= (str.replace s src dst) "a"))
(check-sat)
(reset)

(declare-const a String)
(declare-const b Bool)
;(assert b)
(assert (= b (and (= (str.len a) 3) (str.contains a "a"))))
(check-sat)
(reset)

(declare-const a String)
(assert (and (= (str.len a) 3) (str.contains a "a")))
(check-sat)
(reset)

  (declare-fun s1 () String)
  (declare-fun s2 () String)
  (assert
     (= s1 (str.at "aaa" 2)))
  (assert
     (not (str.contains s1 s2)))
  (check-sat)
(reset)



