
; Copyright (c) 2015 Microsoft Corporation


(get-assertions)

(set-option :interactive-mode true)

(declare-const a Bool)
(declare-const b Bool)

(assert (and a b))
(push)
(assert (or a (let ((x (or a b))) x)))
(push)
(assert (! (or a b) :named foo))
(get-assertions)
(pop)
(get-assertions)
(pop)
(get-assertions)
(pop)
(pop 1000)
(pop -1)
(push 10)
(pop 10)
exit
(exit)
