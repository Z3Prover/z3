(declare-datatypes () ((rec nil (mk (a Int) (b Int) (c Bool)))))
(declare-const x rec)
(push)
(assert ((_ is mk) x))
(assert (not ((_ is mk) ((_ update-field a) x 1))))
(check-sat)
(pop)

(push)
(assert (not ((_ is mk) ((_ update-field a) x 1))))
(check-sat)
(pop)

(push)
(assert (not (= (b x) (b ((_ update-field a) x 1)))))
(check-sat)
(pop)

(push)
(assert (not (= (a x) (a ((_ update-field a) x 1)))))
(check-sat)
(pop)

