module Z3IndependentArrayInterpretation

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module TR = Z3TypedRoot
module A = Z3SortedArray
module AR = Z3IndependentArrayRoot
module AF = Z3IndependentArrayFamily

val target (sigma:V.signature) (f:func_decl)
  : Tot (r:option (sort & sort){
      r == (match f.domain with
            | [ArraySort [index] element; _] ->
              if f = A.ext_decl index element && AR.supports sigma index element
              then Some (index, element) else None
            | _ -> None)})

val symbols (u:TR.uninterpreted) (sch:S.checked_schema) (uf:TR.symbols u sch)
  : GTot (TR.symbols u sch)

val lemma_preserves_other (u:TR.uninterpreted) (sch:S.checked_schema)
  (uf:TR.symbols u sch) (f:func_decl) (xs:TR.targuments u sch f.domain)
  : Lemma (requires None? (target (S.signature sch) f))
          (ensures (symbols u sch uf).TR.apply f xs == uf.TR.apply f xs)

val lemma_preserves_application (u:TR.uninterpreted) (sch:S.checked_schema)
  (uf:TR.symbols u sch) (f:func_decl) (xs:TR.targuments u sch f.domain)
  : Lemma (requires None? (target (S.signature sch) f))
          (ensures (TR.standard u sch (symbols u sch uf)).V.application f xs ==
                   (TR.standard u sch uf).V.application f xs)

val lemma_preserves_quantification (u:TR.uninterpreted) (sch:S.checked_schema)
  (uf:TR.symbols u sch) (k:quantifier_kind) (bound:list sort) (t:sort)
  (body:TR.body_of u sch bound t)
  : Lemma ((TR.standard u sch (symbols u sch uf)).V.quantification k bound t body ==
           (TR.standard u sch uf).V.quantification k bound t body)

val lemma_root_inhabited (u:TR.uninterpreted) (sch:S.checked_schema)
  (uf:TR.symbols u sch)
  : Lemma (TR.root_model u sch (TR.standard u sch (symbols u sch uf)))

val lemma_ext_application (u:TR.uninterpreted) (sch:S.checked_schema)
  (uf:TR.symbols u sch) (index:sort)
  (element:sort{AR.supports (S.signature sch) index element})
  (a b:A.array_value (TR.carrier u) (S.signature sch) index element)
  : Lemma ((TR.standard u sch (symbols u sch uf)).V.application
              (A.ext_decl index element) [a; b] ==
           AR.difference u (S.signature sch) index element a b)

val lemma_model (u:TR.uninterpreted) (sch:S.checked_schema) (uf:TR.symbols u sch)
  : Lemma (A.model sch (TR.booleans u) (Z3SortedRoot.root_scalars u)
      (TR.standard u sch (symbols u sch uf)) (AF.family u (S.signature sch)))
