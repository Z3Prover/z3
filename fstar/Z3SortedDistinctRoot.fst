module Z3SortedDistinctRoot

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module A = Z3DistinctAst
module TR = Z3TypedRoot
module SR = Z3SortedRoot
module D = Z3ExprScope
module K = Z3SortedDistinct

let rec distinct_from (#base:Z3AstTheory.sort -> Type0) (eq:T.scalar_equality base)
                      (v:V.tree base) (vs:list (V.tree base)) : GTot bool (decreases vs) =
  match vs with
  | [] -> true
  | w :: rest -> not (T.equal_tree eq v w) && distinct_from eq v rest

let rec distinct_values (#base:Z3AstTheory.sort -> Type0) (eq:T.scalar_equality base)
                        (vs:list (V.tree base)) : GTot bool (decreases vs) =
  match vs with
  | [] -> true
  | v :: rest -> distinct_from eq v rest && distinct_values eq rest

let standard_symbols (u:TR.uninterpreted) (sch:S.checked_schema)
                     (uf:TR.symbols u sch) : GTot (TR.symbols u sch) =
  { TR.apply = (fun f xs ->
      if A.distinct_declaration f then
        TR.boolean sch (distinct_values (SR.root_equality u) xs)
      else uf.TR.apply f xs);
    TR.lambda = uf.TR.lambda }

let lemma_root_inhabited (u:TR.uninterpreted) (sch:S.checked_schema)
                        (uf:TR.symbols u sch)
  : Lemma (TR.root_model u sch (TR.standard u sch (standard_symbols u sch uf))) =
  TR.lemma_standard_root u sch (standard_symbols u sch uf)

let lemma_preserves_other (u:TR.uninterpreted) (sch:S.checked_schema)
                          (uf:TR.symbols u sch) (f:func_decl{not (A.distinct_declaration f)})
                          (xs:TR.targuments u sch f.domain)
  : Lemma ((standard_symbols u sch uf).TR.apply f xs == uf.TR.apply f xs) = ()

let rec lemma_from_agreement (u:TR.uninterpreted) (sch:S.checked_schema)
                             (i:TR.interp u sch) (scope:list sort)
                             (rho:V.environment (TR.carrier u) (S.signature sch) scope)
                             (a:expr{D.scoped scope a})
                             (args:list expr{D.scoped_args scope args})
                             (ss:list sort{sorts_match args ss})
  : Lemma (
      K.distinct_from_at sch (TR.booleans u) (SR.root_scalars u) i scope rho a args ==
      distinct_from (SR.root_equality u)
        (T.evaluate_at sch (TR.booleans u) (SR.root_scalars u) i scope rho a)
        (T.evaluate_arguments_at sch (TR.booleans u) (SR.root_scalars u) i scope rho args ss))
      (decreases args) =
  match args, ss with
  | [], [] -> K.lemma_from_nil sch (TR.booleans u) (SR.root_scalars u) i scope rho a
  | b :: rest, _ :: tail ->
    K.lemma_from_cons sch (TR.booleans u) (SR.root_scalars u) i scope rho a b rest;
    lemma_from_agreement u sch i scope rho a rest tail
  | _, _ -> ()

let rec lemma_values_agreement (u:TR.uninterpreted) (sch:S.checked_schema)
                               (i:TR.interp u sch) (scope:list sort)
                               (rho:V.environment (TR.carrier u) (S.signature sch) scope)
                               (args:list expr{D.scoped_args scope args})
                               (ss:list sort{sorts_match args ss})
  : Lemma (
      K.distinct_values_at sch (TR.booleans u) (SR.root_scalars u) i scope rho args ==
      distinct_values (SR.root_equality u)
        (T.evaluate_arguments_at sch (TR.booleans u) (SR.root_scalars u) i scope rho args ss))
      (decreases args) =
  match args, ss with
  | [], [] -> K.lemma_values_nil sch (TR.booleans u) (SR.root_scalars u) i scope rho
  | a :: rest, _ :: tail ->
    K.lemma_values_cons sch (TR.booleans u) (SR.root_scalars u) i scope rho a rest;
    lemma_from_agreement u sch i scope rho a rest tail;
    lemma_values_agreement u sch i scope rho rest tail
  | _, _ -> ()

let lemma_distinct_classify (sch:S.checked_schema) (f:func_decl)
  : Lemma (requires A.distinct_declaration f)
          (ensures TR.classify (S.signature sch) f == TR.Other /\ not (TR.datatype_kind f)) = ()

let lemma_distinct_case (u:TR.uninterpreted) (sch:S.checked_schema)
                        (uf:TR.symbols u sch) (scope:list sort)
                        (rho:V.environment (TR.carrier u) (S.signature sch) scope)
                        (f:func_decl) (args:list expr)
  : Lemma (D.scoped scope (App f args) /\ A.distinct_app f args ==>
           (let i = TR.standard u sch (standard_symbols u sch uf) in
            T.truth_at sch (TR.booleans u) (SR.root_scalars u) i scope rho (App f args) ==
            K.distinct_values_at sch (TR.booleans u) (SR.root_scalars u) i scope rho args)) =
  if D.scoped scope (App f args) && A.distinct_app f args then (
    let symbols = standard_symbols u sch uf in
    let i = TR.standard u sch symbols in
    lemma_distinct_classify sch f;
    TR.lemma_standard_root u sch symbols;
    TR.lemma_not_constructor sch f;
    SR.lemma_truth_agreement u sch i scope rho (App f args);
    SR.lemma_evaluate_args_agreement u sch i scope rho args f.domain;
    lemma_values_agreement u sch i scope rho args f.domain;
    let vs = V.evaluate_args (S.signature sch) i scope rho args f.domain in
    TR.lemma_standard_application u sch symbols f vs;
    TR.lemma_truth_boolean #u sch (distinct_values (SR.root_equality u) vs))

let lemma_distinct_model (u:TR.uninterpreted) (sch:S.checked_schema)
                         (uf:TR.symbols u sch)
  : Lemma (K.model sch (TR.booleans u) (SR.root_scalars u)
             (TR.standard u sch (standard_symbols u sch uf))) =
  FStar.Classical.forall_intro_4 (lemma_distinct_case u sch uf)
