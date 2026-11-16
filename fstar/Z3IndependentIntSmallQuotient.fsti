module Z3IndependentIntSmallQuotient

module DV = Z3SortedIntDivision

val lemma_small_quotient (x d:int)
  : Lemma (requires 0 <= x /\ x < d)
          (ensures DV.quotient_of x d == 0)
