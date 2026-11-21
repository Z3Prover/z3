module Z3IndependentFiniteFieldRoot

module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module TR = Z3TypedRoot
module FF = Z3SortedFiniteField
module SR = Z3SortedRoot
module T = Z3SortedSemantics
module R = Z3ClauseSyntax
module Replay = Z3IndependentFiniteFieldReplay
module D = Z3ExprScope
module FE = FStar.FunctionalExtensionality
module L = FStar.List.Tot
open Z3AstTheory
open FStar.List.Tot

let project (u:TR.uninterpreted) (p:int{p > 1})
            (v:V.tree (TR.carrier u)) : Tot int =
  match v with
  | V.Scalar t x -> if t = FF.ff_sort p then (x <: int) else 0
  | V.Constructor _ _ -> 0

let lemma_project_range (u:TR.uninterpreted) (sch:S.checked_schema)
                        (p:int{p > 1}) (v:V.tree (TR.carrier u))
  : Lemma (requires not (V.datatype_sort (S.signature sch) (FF.ff_sort p)) /\
                    V.has_sort (S.signature sch) (FF.ff_sort p) v)
          (ensures 0 <= project u p v /\ project u p v < p) =
  match v with
  | V.Scalar _ _ -> ()
  | V.Constructor f _ -> TR.lemma_registered (S.signature sch) f

let lemma_project_reflection (u:TR.uninterpreted) (sch:S.checked_schema)
                             (p:int{p > 1}) (x y:V.tree (TR.carrier u))
  : Lemma (requires not (V.datatype_sort (S.signature sch) (FF.ff_sort p)) /\
                    V.has_sort (S.signature sch) (FF.ff_sort p) x /\
                    V.has_sort (S.signature sch) (FF.ff_sort p) y)
          (ensures (x == y <==> project u p x == project u p y)) =
  match x, y with
  | V.Scalar _ _, V.Scalar _ _ -> ()
  | V.Constructor f _, _ -> TR.lemma_registered (S.signature sch) f
  | _, V.Constructor f _ -> TR.lemma_registered (S.signature sch) f

let lemma_calculate_range (p:int{p > 1}) (op:Z3AstTheory.decl_kind) (xs:list int)
  : Lemma (0 <= FF.calculate p op xs /\ FF.calculate p op xs < p) =
  if op = FF.op_ff_add then
    (match xs with [] -> () | _ :: _ -> ())
  else if op = FF.op_ff_mul then
    (match xs with [] -> () | _ :: _ -> ())
  else if op = FF.op_ff_bitsum then
    (match xs with [] -> () | _ :: _ -> ())
  else match xs with [_] -> () | _ -> ()

let field_application (u:TR.uninterpreted) (sch:S.checked_schema)
                      (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
                      (other:TR.interp u sch) (f:Z3AstTheory.func_decl)
                      (xs:TR.targuments u sch f.domain)
  : GTot (TR.tvalue u sch f.range) =
  match FF.numeral (Z3AstTheory.App f []) with
  | Some (q, n) ->
    if q = p then TR.make #u #(S.signature sch) (FF.ff_sort p) n
    else other.application f xs
  | None ->
    (match FF.operation_of f with
     | Some (q, op) ->
       if q = p then (
         let value = FF.calculate p op (FF.projections (project u p) xs) in
         lemma_calculate_range p op (FF.projections (project u p) xs);
         TR.make #u #(S.signature sch) (FF.ff_sort p) value)
       else other.application f xs
     | None -> other.application f xs)

let model (u:TR.uninterpreted) (sch:S.checked_schema)
          (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
          (other:TR.interp u sch) : GTot (FF.model (TR.carrier u) sch p) =
  { FF.booleans = TR.booleans u;
    FF.scalar_model = SR.root_scalars u;
    FF.other = other;
    FF.field_sort_is_scalar = ();
    FF.project = project u p;
    FF.project_range = lemma_project_range u sch p;
    FF.project_reflection = lemma_project_reflection u sch p;
    FF.field_application = field_application u sch p other;
    FF.numeral_law = (fun f n -> ());
    FF.operation_law = (fun f xs op -> ()) }

let field_symbols (u:TR.uninterpreted) (sch:S.checked_schema)
                  (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
                  (uf:TR.symbols u sch) : GTot (TR.symbols u sch) =
  { TR.apply = field_application u sch p (TR.standard u sch uf);
    TR.lambda = uf.TR.lambda }

let lemma_root_inhabited (u:TR.uninterpreted) (sch:S.checked_schema)
                         (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
                         (uf:TR.symbols u sch)
  : Lemma (TR.root_model u sch (TR.standard u sch (field_symbols u sch p uf))) =
  TR.lemma_standard_root u sch (field_symbols u sch p uf)

let lemma_preserves_other (u:TR.uninterpreted) (sch:S.checked_schema)
                          (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
                          (uf:TR.symbols u sch) (f:func_decl)
                          (xs:TR.targuments u sch f.domain)
  : Lemma (requires (match FF.numeral (App f []) with Some (q, _) -> q <> p | None -> True) /\
                    (match FF.operation_of f with Some (q, _) -> q <> p | None -> True))
          (ensures (field_symbols u sch p uf).TR.apply f xs == (TR.standard u sch uf).V.application f xs) = ()

let lemma_field_classification (sch:S.checked_schema) (p:int{p > 1})
                               (f:Z3AstTheory.func_decl)
  : Lemma (requires (Some? (FF.numeral (Z3AstTheory.App f [])) /\
                     fst (Some?.v (FF.numeral (Z3AstTheory.App f []))) == p) \/
                    (Some? (FF.operation_of f) /\
                     fst (Some?.v (FF.operation_of f)) == p))
          (ensures TR.classify (S.signature sch) f == TR.Other /\ not (TR.datatype_kind f)) = ()

let lemma_override_application (u:TR.uninterpreted) (sch:S.checked_schema)
                               (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
                               (uf:TR.symbols u sch) (f:Z3AstTheory.func_decl)
                               (xs:TR.targuments u sch f.domain)
  : Lemma (
    let root = TR.standard u sch (field_symbols u sch p uf) in
    (FF.override sch p (model u sch p root)).V.application f xs ==
    root.V.application f xs) =
  let symbols = field_symbols u sch p uf in
  match FF.numeral (Z3AstTheory.App f []) with
  | Some (q, _) ->
    if q = p then (
      lemma_field_classification sch p f;
      TR.lemma_standard_application u sch symbols f xs)
  | None ->
    (match FF.operation_of f with
     | Some (q, _) ->
       if q = p then (
         lemma_field_classification sch p f;
         TR.lemma_standard_application u sch symbols f xs)
     | None -> ())

let lemma_sorted_application (u:TR.uninterpreted) (sch:S.checked_schema)
                             (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
                             (uf:TR.symbols u sch) (f:func_decl)
                             (xs:TR.targuments u sch f.domain)
  : Lemma (
    let root = TR.standard u sch (field_symbols u sch p uf) in
    T.application sch (TR.booleans u) (SR.root_scalars u)
      (FF.override sch p (model u sch p root)) f xs == root.V.application f xs) =
  let root = TR.standard u sch (field_symbols u sch p uf) in
  lemma_root_inhabited u sch p uf;
  lemma_override_application u sch p uf f xs;
  SR.lemma_application_agreement u sch root f xs

let rec lemma_sorted_evaluate (u:TR.uninterpreted) (sch:S.checked_schema)
                              (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
                              (uf:TR.symbols u sch) (scope:list sort)
                              (rho:V.environment (TR.carrier u) (S.signature sch) scope)
                              (e:expr{D.scoped scope e})
  : Lemma (
    let root = TR.standard u sch (field_symbols u sch p uf) in
    T.evaluate_at sch (TR.booleans u) (SR.root_scalars u)
      (FF.override sch p (model u sch p root)) scope rho e ==
    V.evaluate (S.signature sch) root scope rho e)
    (decreases %[(V.expression_size e <: nat); (0 <: nat)]) =
  let sigma = S.signature sch in
  let root = TR.standard u sch (field_symbols u sch p uf) in
  let field = T.interpretation sch (TR.booleans u) (SR.root_scalars u)
    (FF.override sch p (model u sch p root)) in
  match e with
  | Var _ _ -> ()
  | App f args ->
    lemma_sorted_arguments u sch p uf scope rho args f.domain;
    if not (L.mem f sigma) then
      lemma_sorted_application u sch p uf f (V.evaluate_args sigma root scope rho args f.domain)
  | Quantifier k bound _ body ->
    let left = V.evaluate_body sigma field scope rho bound body in
    let right = V.evaluate_body sigma root scope rho bound body in
    let pointwise (vs:TR.targuments u sch (L.rev bound)) : Lemma (left vs == right vs) =
      lemma_sorted_evaluate u sch p uf (L.rev bound @ scope)
        (V.extend sigma scope (L.rev bound) vs rho) body in
    FStar.Classical.forall_intro pointwise;
    assert (FE.feq_g left right);
    FE.extensionality_g (TR.targuments u sch (L.rev bound)) (fun _ -> V.tree (TR.carrier u)) left right;
    assert (left == right);
    assert (field.V.quantification == root.V.quantification);
    assert (V.evaluate sigma field scope rho e ==
            root.V.quantification k bound (get_sort body) (V.typed_body sigma bound (get_sort body) left));
    assert (V.evaluate sigma root scope rho e ==
            root.V.quantification k bound (get_sort body) (V.typed_body sigma bound (get_sort body) right))

and lemma_sorted_arguments (u:TR.uninterpreted) (sch:S.checked_schema)
                           (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
                           (uf:TR.symbols u sch) (scope:list sort)
                           (rho:V.environment (TR.carrier u) (S.signature sch) scope)
                           (es:list expr{D.scoped_args scope es}) (ss:list sort{sorts_match es ss})
  : Lemma (
    let root = TR.standard u sch (field_symbols u sch p uf) in
    V.evaluate_args (S.signature sch)
      (T.interpretation sch (TR.booleans u) (SR.root_scalars u)
        (FF.override sch p (model u sch p root))) scope rho es ss ==
    V.evaluate_args (S.signature sch) root scope rho es ss)
    (decreases %[(V.expressions_size es <: nat); (1 <: nat)]) =
  match es, ss with
  | e :: rest, s :: remaining ->
    V.lemma_sort_eq (get_sort e) s;
    lemma_sorted_evaluate u sch p uf scope rho e;
    lemma_sorted_arguments u sch p uf scope rho rest remaining
  | _, _ -> ()

let lemma_truth_agreement (u:TR.uninterpreted) (sch:S.checked_schema)
                          (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
                          (uf:TR.symbols u sch) (e:expr)
  : Lemma (
    let root = TR.standard u sch (field_symbols u sch p uf) in
    T.truth sch (TR.booleans u) (SR.root_scalars u)
      (FF.override sch p (model u sch p root)) e ==
    T.truth sch (TR.booleans u) (SR.root_scalars u) root e) =
  if D.scoped [] e && get_sort e = bool_sort then (
    let root = TR.standard u sch (field_symbols u sch p uf) in
    let rho = T.empty_environment (S.signature sch) in
    lemma_root_inhabited u sch p uf;
    lemma_sorted_evaluate u sch p uf [] rho e;
    SR.lemma_evaluate_agreement u sch root [] rho e)

let lemma_rewrite (u:TR.uninterpreted) (sch:S.checked_schema)
                  (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
                  (uf:TR.symbols u sch) (a b:expr)
  : Lemma (requires Replay.rewrite p a b)
          (ensures T.truth sch (TR.booleans u) (SR.root_scalars u)
            (TR.standard u sch (field_symbols u sch p uf)) (R.mk_eq_expr a b)) =
  let root = TR.standard u sch (field_symbols u sch p uf) in
  Replay.lemma_rewrite sch p (model u sch p root) a b;
  lemma_truth_agreement u sch p uf (R.mk_eq_expr a b)

let lemma_clause (u:TR.uninterpreted) (sch:S.checked_schema)
                 (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
                 (uf:TR.symbols u sch) (e:expr)
  : Lemma (requires Replay.clause p e)
          (ensures T.truth sch (TR.booleans u) (SR.root_scalars u)
            (TR.standard u sch (field_symbols u sch p uf)) e) =
  let root = TR.standard u sch (field_symbols u sch p uf) in
  Replay.lemma_clause sch p (model u sch p root) e;
  lemma_truth_agreement u sch p uf e

let lemma_pac (u:TR.uninterpreted) (sch:S.checked_schema)
              (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
              (uf:TR.symbols u sch) (c:FF.certificate) (e:expr)
  : Lemma (requires Replay.pac p c e)
          (ensures T.truth sch (TR.booleans u) (SR.root_scalars u)
            (TR.standard u sch (field_symbols u sch p uf)) e) =
  let root = TR.standard u sch (field_symbols u sch p uf) in
  Replay.lemma_pac sch p (model u sch p root) c e;
  lemma_truth_agreement u sch p uf e

let lemma_pac_with_evidence (u:TR.uninterpreted) (sch:S.checked_schema)
              (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
              (uf:TR.symbols u sch) (c:FF.certificate) (e:expr)
              (evidence:option (int & list int))
  : Lemma (requires Replay.pac_with_evidence p c e evidence)
          (ensures T.truth sch (TR.booleans u) (SR.root_scalars u)
            (TR.standard u sch (field_symbols u sch p uf)) e) =
  let root = TR.standard u sch (field_symbols u sch p uf) in
  Replay.lemma_pac_with_evidence sch p (model u sch p root) c e evidence;
  lemma_truth_agreement u sch p uf e

let lemma_pac_for_prime (u:TR.uninterpreted) (sch:S.checked_schema)
              (p:int{FStar.Math.Euclid.is_prime p /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
              (uf:TR.symbols u sch) (c:FF.certificate) (e:expr)
  : Lemma (requires Replay.pac_for_prime p c e)
          (ensures T.truth sch (TR.booleans u) (SR.root_scalars u)
            (TR.standard u sch (field_symbols u sch p uf)) e) =
  let root = TR.standard u sch (field_symbols u sch p uf) in
  Replay.lemma_pac_for_prime sch p (model u sch p root) c e;
  lemma_truth_agreement u sch p uf e
