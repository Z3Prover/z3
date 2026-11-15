module Z3IndependentArrayInterpretation

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module TR = Z3TypedRoot
module A = Z3SortedArray
module AR = Z3IndependentArrayRoot
module AF = Z3IndependentArrayFamily
module SR = Z3SortedRoot

let target (sigma:V.signature) (f:func_decl)
  : Tot (r:option (sort & sort){
      r == (match f.domain with
            | [ArraySort [index] element; _] ->
              if f = A.ext_decl index element && AR.supports sigma index element
              then Some (index, element) else None
            | _ -> None)}) =
  match f.domain with
  | [ArraySort [index] element; _] ->
    if f = A.ext_decl index element && AR.supports sigma index element
    then Some (index, element) else None
  | _ -> None

let symbols (u:TR.uninterpreted) (sch:S.checked_schema) (uf:TR.symbols u sch)
  : GTot (TR.symbols u sch) =
  let sigma = S.signature sch in
  let apply (f:func_decl) (xs:TR.targuments u sch f.domain)
    : GTot (TR.tvalue u sch f.range) =
    match target sigma f with
    | Some (index, element) ->
      (match xs with
       | [a; b] -> AR.difference u sigma index element a b
       | _ -> FStar.Pervasives.false_elim ())
    | None -> uf.TR.apply f xs in
  { TR.apply = apply; TR.lambda = uf.TR.lambda }

let lemma_preserves_other (u:TR.uninterpreted) (sch:S.checked_schema)
                          (uf:TR.symbols u sch) (f:func_decl) (xs:TR.targuments u sch f.domain)
  : Lemma (requires None? (target (S.signature sch) f))
          (ensures (symbols u sch uf).TR.apply f xs == uf.TR.apply f xs) = ()

let lemma_preserves_application (u:TR.uninterpreted) (sch:S.checked_schema)
                                (uf:TR.symbols u sch) (f:func_decl)
                                (xs:TR.targuments u sch f.domain)
  : Lemma (requires None? (target (S.signature sch) f))
          (ensures (TR.standard u sch (symbols u sch uf)).V.application f xs ==
                   (TR.standard u sch uf).V.application f xs) =
  let sigma = S.signature sch in
  if FStar.List.Tot.mem f sigma then ()
  else match S.find_recognizer f sch.cases with
  | Some _ -> ()
  | None ->
    (match S.find_accessor f sch.cases with
     | Some _ ->
       (match xs with
        | [v] ->
          lemma_preserves_other u sch uf f [v]
        | _ -> ())
     | None -> lemma_preserves_other u sch uf f xs)

let lemma_preserves_quantification (u:TR.uninterpreted) (sch:S.checked_schema)
                                   (uf:TR.symbols u sch) (k:quantifier_kind)
                                   (bound:list sort) (t:sort) (body:TR.body_of u sch bound t)
  : Lemma ((TR.standard u sch (symbols u sch uf)).V.quantification k bound t body ==
           (TR.standard u sch uf).V.quantification k bound t body) = ()

let lemma_root_inhabited (u:TR.uninterpreted) (sch:S.checked_schema)
                         (uf:TR.symbols u sch)
  : Lemma (TR.root_model u sch (TR.standard u sch (symbols u sch uf))) =
  TR.lemma_standard_root u sch (symbols u sch uf)

let lemma_ext_application (u:TR.uninterpreted) (sch:S.checked_schema)
                          (uf:TR.symbols u sch) (index:sort)
                          (element:sort{AR.supports (S.signature sch) index element})
                          (a b:A.array_value (TR.carrier u) (S.signature sch) index element)
  : Lemma ((TR.standard u sch (symbols u sch uf)).V.application
              (A.ext_decl index element) [a; b] ==
           AR.difference u (S.signature sch) index element a b) =
  TR.lemma_standard_application u sch (symbols u sch uf) (A.ext_decl index element) [a; b]

let lemma_model (u:TR.uninterpreted) (sch:S.checked_schema) (uf:TR.symbols u sch)
  : Lemma (A.model sch (TR.booleans u) (SR.root_scalars u)
      (TR.standard u sch (symbols u sch uf)) (AF.family u (S.signature sch))) =
  let sigma = S.signature sch in
  let fs = symbols u sch uf in
  let root = TR.standard u sch fs in
  let m = AF.family u sigma in
  lemma_root_inhabited u sch uf;
  let select (index:sort) (element:sort{m.A.supports index element})
             (a:A.array_value (TR.carrier u) sigma index element)
             (k:V.value (TR.carrier u) sigma index)
    : Lemma (Z3SortedSemantics.application sch (TR.booleans u) (SR.root_scalars u)
               root (A.select_decl index element) [a; k] ==
             (m.A.arrays index element).A.read a k) =
    SR.lemma_application_agreement u sch root (A.select_decl index element) [a; k];
    AR.lemma_root_read u sch root index element a k in
  let store (index:sort) (element:sort{m.A.supports index element})
            (a:A.array_value (TR.carrier u) sigma index element)
            (k:V.value (TR.carrier u) sigma index) (v:V.value (TR.carrier u) sigma element)
    : Lemma (Z3SortedSemantics.application sch (TR.booleans u) (SR.root_scalars u)
               root (A.store_decl index element) [a; k; v] ==
             (m.A.arrays index element).A.write a k v) =
    SR.lemma_application_agreement u sch root (A.store_decl index element) [a; k; v];
    AR.lemma_root_write u sch root index element a k v in
  let ext (index:sort) (element:sort{m.A.supports index element})
          (a b:A.array_value (TR.carrier u) sigma index element)
    : Lemma (Z3SortedSemantics.application sch (TR.booleans u) (SR.root_scalars u)
               root (A.ext_decl index element) [a; b] ==
             (m.A.arrays index element).A.difference a b) =
    SR.lemma_application_agreement u sch root (A.ext_decl index element) [a; b];
    lemma_ext_application u sch uf index element a b in
  let store_prefix (index:sort) (element:sort{m.A.supports index element})
                   (a:A.array_value (TR.carrier u) sigma index element)
                   (k:V.value (TR.carrier u) sigma index)
    : Lemma (forall (v:V.value (TR.carrier u) sigma element).
        Z3SortedSemantics.application sch (TR.booleans u) (SR.root_scalars u)
          root (A.store_decl index element) [a; k; v] ==
        (m.A.arrays index element).A.write a k v) =
    FStar.Classical.forall_intro (store index element a k) in
  FStar.Classical.forall_intro_4 select;
  FStar.Classical.forall_intro_4 store_prefix;
  FStar.Classical.forall_intro_4 ext
