module Z3ObservationalSyntax

open Z3AstTheory
open Z3OperatorTags
module OS = Z3ObservationalSemantics

let typed_oeq_decl (s:sort) : func_decl =
  { decl_name = "~"; domain = [s; s]; range = bool_sort;
    interp = Some op_oeq; int_params = [] }

let oeq_decl : func_decl = typed_oeq_decl bool_sort

let mk_oeq_expr (a b:expr) : expr = App (typed_oeq_decl (get_sort a)) [a; b]

let is_oeq (e:expr) : option (expr & expr) =
  match e with
  | App f [a; b] ->
    if f = typed_oeq_decl (get_sort a) && get_sort a = get_sort b
    then Some (a, b) else None
  | _ -> None

let decide_mp_oeq (a relation:expr) : option expr =
  match is_oeq relation with
  | Some (s, t) -> if a = s then Some t else None
  | None -> None

let lemma_decide_mp_oeq (#value:Type) (#domain:expr -> bool)
                        (vtrue:value) (denote:OS.denotation value domain)
                        (a:expr{domain a}) (relation:expr)
  : Lemma (requires Some? (decide_mp_oeq a relation) /\ denote a == vtrue /\
                    (match is_oeq relation with
                     | Some (s, t) -> domain s /\ domain t /\ OS.observations_agree vtrue denote s t
                     | None -> False))
          (ensures domain (Some?.v (decide_mp_oeq a relation)) /\
                   denote (Some?.v (decide_mp_oeq a relation)) == vtrue) =
  match is_oeq relation with
  | Some (s, t) -> OS.lemma_mp vtrue denote s t
  | None -> ()
