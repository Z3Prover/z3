; Advanced: Drinker's paradox (higher-order encoding)
(set-logic HO_ALL)
(declare-sort Person 0)
(declare-fun drinks () (-> Person Bool))
; There exists a person such that if they drink, everyone drinks
(assert (not (exists ((p Person))
  (=> (drinks p) (forall ((q Person)) (drinks q))))))
(check-sat)
(exit)
