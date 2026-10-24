; select_store_diff -- the array rewrite `select(store(a,i,x),j) =
; select(a,j)` for `i <> j`. This pattern *is* now a verified matcher
; (Z3PatternMatchedProofChecker.fst section 4i,
; `match_select_store_diff`/`select_store_diff_leaf_ok`), added after an
; `uninterp_app` model fix (distinctly-named 0-ary constants now denote
; distinct values, via an injective string encoding). This *specific*
; example, however, still logs its single Rewrite leaf as matched by
; `reflexivity`, not `select_store_diff`: Z3's own proof search discharges
; the array fact here via `PR_TH_LEMMA` (a theory-lemma proof step this
; checker trusts unconditionally -- it is outside the `Rewrite`-leaf
; matcher's scope entirely), and the only literal `Rewrite` leaf left over
; is Z3's self-rewrite of the asserted `(not (= i j))` hypothesis. See
; `Z3ExtractedProof_SelectStoreDiff.fst.unmatched.log` for the generated
; proof's actual leaf. `select_store_diff` *does* fire for real on other
; proofs, confirmed on the QF_AX SMT-LIB benchmark corpus (see
; QF_AX_QF_UF_BENCHMARK_REPORT.md).
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(declare-const x Int)
(assert (not (= i j)))
(assert (not (= (select (store a i x) j) (select a j))))
(check-sat)
