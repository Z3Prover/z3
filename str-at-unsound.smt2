; Reduced from QF_SLIA restoreIpAddresses benchmarks.
; Before the mem_propagation stale-view fix:
;   smt.string_solver=seq  -> sat
;   smt.string_solver=nseq -> unsat
; After the stale-view fix, nseq returns unknown instead of false UNSAT.
; With symbolic derivative and disequality completion, search returns SAT,
; but model validation still rejects the generated model.
; "0" is a satisfying value for s.
(set-logic QF_SLIA)
(declare-const s String)
(assert (= (str.to_int (str.at s 0)) 0))
(check-sat)
