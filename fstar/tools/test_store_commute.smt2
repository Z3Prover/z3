; store_commute -- `store(store(a,i,x),j,y) = store(store(a,j,y),i,x)`
; for `i <> j`, the index-swap twin of select_store_diff.
; Historical exporter/matcher fixture; that pipeline is retired.
; Z3 may use array extensionality/theory lemmas instead of adjacent
; rewrite steps. Historical rewrite coverage measurements are in
; QF_AX_QF_UF_BENCHMARK_REPORT.md.
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(declare-const x Int)
(declare-const y Int)
(assert (not (= i j)))
(assert (not (= (store (store a i x) j y) (store (store a j y) i x))))
(check-sat)
