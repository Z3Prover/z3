module Z3SortedDistinctRoot

module S = Z3DatatypeSignature
module TR = Z3TypedRoot
module SR = Z3SortedRoot
module K = Z3SortedDistinct
module A = Z3DistinctAst
open Z3AstTheory

val standard_symbols (u:TR.uninterpreted) (sch:S.checked_schema)
  (uf:TR.symbols u sch) : GTot (TR.symbols u sch)

val lemma_root_inhabited (u:TR.uninterpreted) (sch:S.checked_schema)
  (uf:TR.symbols u sch)
  : Lemma (TR.root_model u sch (TR.standard u sch (standard_symbols u sch uf)))

val lemma_preserves_other (u:TR.uninterpreted) (sch:S.checked_schema)
  (uf:TR.symbols u sch) (f:func_decl{not (A.distinct_declaration f)})
  (xs:TR.targuments u sch f.domain)
  : Lemma ((standard_symbols u sch uf).TR.apply f xs == uf.TR.apply f xs)

val lemma_distinct_model (u:TR.uninterpreted) (sch:S.checked_schema)
  (uf:TR.symbols u sch)
  : Lemma (K.model sch (TR.booleans u) (SR.root_scalars u)
             (TR.standard u sch (standard_symbols u sch uf)))
