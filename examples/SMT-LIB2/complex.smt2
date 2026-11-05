; Complex arithmetic is lowered to Real arithmetic.
(declare-const z Complex)
(assert (= (* z z) (complex.make (- 1) 0)))
(check-sat)
(get-model)
(get-value ((complex.real z) (complex.imag z)))

; The constructor and projections describe exactly a pair of Reals.
(push)
(assert (distinct z (complex.make (complex.real z) (complex.imag z))))
(check-sat)
(pop)
