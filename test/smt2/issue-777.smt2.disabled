; Copyright (c) 2016 Microsoft Corporation

;(set-option :fp.engine spacer)
(declare-rel nondet2 ((_ BitVec 2) Bool))
(declare-var A (_ BitVec 2))
(declare-var H (_ BitVec 2))
(declare-var F Bool)
(rule (nondet2 #b10 false))
(rule (nondet2 #b01 true))
(declare-rel q!!1 ())
(rule (=> (and (nondet2 H F) (nondet2 A F) (not (= H #b01))) q!!1))
(query q!!1)
