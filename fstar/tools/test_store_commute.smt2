; store_commute -- `store(store(a,i,x),j,y) = store(store(a,j,y),i,x)`
; for `i <> j`, the index-swap twin of select_store_diff. This pattern
; *is* now a verified matcher (Z3PatternMatchedProofChecker.fst section
; 4j, `match_store_commute`/`store_commute_leaf_ok`), and it does fire on
; this hand-built, single-level example. Re-running the full QF_AX
; corpus, however, shows it adds *zero* additional matches there: Z3's
; `storecomm_*` benchmark family proves the entire multi-level
; permutation (4+ nested `store`s) in a single `(_ array-ext 0)`
; witness/theory-lemma leap, not as a chain of adjacent one-step swaps,
; so no literal `Rewrite` leaf in those proofs has the flat two-level
; shape this (or any purely single-step) matcher recognizes -- see
; QF_AX_QF_UF_BENCHMARK_REPORT.md's second "Update" section for the
; concrete leaf example and the honest finding. This *specific* example
; file, meanwhile, logs its single Rewrite leaf as unmatched too (same
; `PR_TH_LEMMA`/`array-ext`-witness situation as
; `test_select_store_diff.smt2`'s sibling example) -- see
; `Z3ExtractedProof_StoreCommute.fst.unmatched.log` for the generated
; proof's actual leaf, and `lemma_sc_leaf_true` in
; `Z3PatternMatchedProofChecker.fst` section 11 for an in-source
; demonstration where the matcher genuinely fires.
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(declare-const x Int)
(declare-const y Int)
(assert (not (= i j)))
(assert (not (= (store (store a i x) j y) (store (store a j y) i x))))
(check-sat)
