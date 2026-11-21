module Z3RelationalRuleSyntax

open Z3AstTheory
open Z3UnifiedProofSyntax
module Cong = Z3CongruenceSyntax
module L = FStar.List.Tot

let core_rule (kind:rule) : bool =
  match kind with
  | Reflexivity | Symmetry | Transitivity | TransitivityPath
  | Congruence | IffObservational -> true
  | _ -> false

let step (kind:rule) (r:relation) (a b:expr) (facts:list judgment) : bool =
  match kind with
  | Reflexivity -> facts = [] && a = b
  | Symmetry ->
    (match facts with
     | [j] ->
       (match relational j with
        | Some (r', s, t) -> r = r' && a = t && b = s
        | None -> false)
     | _ -> false)
  | Transitivity ->
    (match facts with
     | [p; q] ->
       (match edge r p, edge r q with
        | Some (s, t), Some (u, v) -> a = s && t = u && b = v
        | _, _ -> false)
     | _ -> false)
  | TransitivityPath ->
    all_edges r facts && L.mem b (reachable (L.length facts) r facts [a])
  | Congruence -> Cong.step r a b facts
  | IffObservational ->
    (match r, facts with
     | Observation, [Equal s t] -> get_sort a = bool_sort && a = s && b = t
     | _, _ -> false)
  | _ -> false
