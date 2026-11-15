; select_store_diff -- `select(store(a,i,x),j) = select(a,j)` for `i <> j`.
; Historical exporter/matcher fixture; that pipeline is retired.
; Z3 may discharge the array fact through a theory lemma rather than
; a literal rewrite. Historical rewrite coverage measurements are in
; QF_AX_QF_UF_BENCHMARK_REPORT.md.
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(declare-const x Int)
(assert (not (= i j)))
(assert (not (= (select (store a i x) j) (select a j))))
(check-sat)
