; Complex arithmetic is lowered to Real arithmetic.
(declare-const z Complex)
(assert (= (* z z) (complex (- 1) 0)))
(check-sat)
(get-model)
(get-value ((real z) (imag z)))

; The constructor and projections describe exactly a pair of Reals.
(push)
(assert (distinct z (complex (real z) (imag z))))
(check-sat)
(pop)
