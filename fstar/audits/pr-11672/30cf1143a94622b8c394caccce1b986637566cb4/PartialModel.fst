module PartialModel
(* Abstract model of PR #11672 partial-model paths. A model is a list of
   (decl, value-option) interpretations; a converter is a partial step. *)
type model = list (nat & int)
type conv = model -> option model   (* None = apply_partial returns false *)

(* concat_model_converter::apply_partial *)
let concat_partial (c1 c2: conv) (m: model) : option model =
  match c2 m with
  | None -> None
  | Some m' -> c1 m'

(* Obligation 1: concat succeeds iff both succeed, c2 applied first,
   matching operator() order; failure of either is never masked. *)
let ob1 (c1 c2: conv) (m: model)
  : Lemma (match concat_partial c1 c2 m with
           | None -> (c2 m == None) \/ (exists m'. c2 m == Some m' /\ c1 m' == None)
           | Some r -> (exists m'. c2 m == Some m' /\ c1 m' == Some r))
  = match c2 m with
    | None -> ()
    | Some m' -> ()

(* Z3_goal_get_model guards *)
type result = | Err | Mdl : model -> bool -> result  (* model, symbolic flag *)

let goal_get_model (enabled: bool) (mc: option conv) : result =
  if not enabled then Err
  else
    match mc with
    | None -> Mdl [] true
    | Some c -> (match c [] with None -> Err | Some m -> Mdl m true)

(* Obligation 2: a model is returned only if enabled, any converter accepted
   starting from the empty model, and the result is flagged symbolic. *)
let ob2 (enabled: bool) (mc: option conv)
  : Lemma (match goal_get_model enabled mc with
           | Err -> (not enabled) \/ (Some? mc /\ (Some?.v mc) [] == None)
           | Mdl m s -> enabled /\ s = true /\
               (match mc with None -> m == [] | Some c -> c [] == Some m))
  = ()

(* Symbolic evaluator lookup: with m_symbolic, a missing interpretation is
   never replaced by a default; with completion it is. *)
let lookup (symbolic: bool) (dflt: int) (m: model) (d: nat) : option int =
  match List.Tot.assoc d m with
  | Some v -> Some v
  | None -> if symbolic then None else Some dflt

(* Obligation 3: symbolic lookup never invents values; interpreted decls agree
   with the non-symbolic lookup. *)
let ob3 (dflt: int) (m: model) (d: nat)
  : Lemma (ensures
      (None? (List.Tot.assoc d m) ==> lookup true dflt m d == None) /\
      (Some? (List.Tot.assoc d m) ==> lookup true dflt m d == lookup false dflt m d))
  = ()
