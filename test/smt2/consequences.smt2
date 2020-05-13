(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-const d Bool)
(declare-const e Bool)

(assert (=> a b))
(assert (=> b c))

(get-consequences ((not c) d) (a b c d c))
