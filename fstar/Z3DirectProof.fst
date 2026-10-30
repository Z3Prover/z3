module Z3DirectProof

open FStar.All
open Z3AstTheory
open Z3ValueTheory
open Z3UnifiedProof
open Z3ProofIndex
module P = Z3ProofDocument
module T = Z3Tptp
module L = FStar.List.Tot

(* Like Z3Tptp, this is a presentation pass run only after kernel acceptance. *)
let unsupported (#a:Type) (message:string) : ML a =
  Z3Native.fail ("Direct proof export: " ^ message)

type problem = {
  document: P.document;
  goal: T.literal;
}

type derived = {
  name: string;
  scope: list sort;
  values: list T.literal;
  hypotheses: list expr;
  uses_goal: bool;
}

let complement ((positive, atom):T.literal) : T.literal = not positive, atom

let contains (values:list T.literal) ((positive, atom):T.literal) : bool =
  not (L.for_all (fun (other, e) -> positive <> other || not (T.same_atom atom e)) values)

let subset (xs ys:list T.literal) : bool = L.for_all (contains ys) xs

let add (values:list T.literal) (value:T.literal) : list T.literal =
  if contains values value then values else L.append values [value]

let union (xs ys:list T.literal) : list T.literal = L.fold_left add xs ys

let is_assumption (p:problem) (e:expr) : ML bool =
  let scope, body = T.universal_scope [] e in
  let values = T.literals true body in
  scope = [] && T.same_literals values [complement p.goal]

let rec remove (value:T.literal) (values:list T.literal)
  : Tot (list T.literal) (decreases values) =
  match values with
  | [] -> []
  | head :: rest ->
    if contains [value] head then remove value rest else head :: remove value rest

let ground_literal (doc:P.document) (e:expr) : ML T.literal =
  let scope, body = T.universal_scope [] e in
  let values = T.literals true body in
  match scope, values with
  | [], [value] ->
    let _rendered = T.render_literals doc [] [value] in
    value
  | _ -> unsupported "expected a ground literal assumption or resolution unit"

let rec guards (doc:P.document) (hyps:list expr) : ML (list T.literal) =
  match hyps with
  | [] -> []
  | h :: rest ->
    let value = ground_literal doc h in
    let rest = guards doc rest in
    complement value :: rest

let lifted (p:problem) (name:string) (formula:expr)
           (hyps:list expr) (uses_goal:bool) : ML derived =
  let scope, body = T.universal_scope [] formula in
  let values = T.literals true body in
  let assumptions = guards p.document hyps in
  let values = union [] (L.append values assumptions) in
  let values = if uses_goal then add values p.goal else values in
  let _rendered = T.render_clause p.document scope values in
  { name = name; scope = scope; values = values;
    hypotheses = hyps; uses_goal = uses_goal }

let emit (p:problem) (result:derived) (rule:string) (parents:list string)
         (lines:list string) : ML (list string) =
  let formula = T.render_clause p.document result.scope result.values in
  T.inference p.document result.name formula rule parents :: lines

let finish (p:problem) (id:int) (formula:expr) (hyps:list expr) (uses_goal:bool)
           (source:derived) (lines:list string) : ML (derived & list string) =
  let target = lifted p ("p" ^ string_of_int id) formula hyps uses_goal in
  if source.scope <> target.scope || not (subset source.values target.values)
  then unsupported ("unsupported lifted conclusion at proof entry " ^ string_of_int id)
  else if subset target.values source.values
  then { target with name = source.name }, lines
  else target, emit p target "weakening" [source.name] lines

let rec visit (fuel:nat) (p:problem) (id:int)
              (seen:index_tree derived) (lines:list string)
  : ML (derived & index_tree derived & list string) =
  if fuel = 0 then unsupported "cyclic or oversized proof"
  else if id < 0 then unsupported "negative proof entry reference"
  else match index_get seen id with
  | Some result -> result, seen, lines
  | None ->
    let e = T.entry_at id p.document.entries in
    let name = "p" ^ string_of_int id in
    let result, seen, lines =
      match e.P.rule, e.P.premise_ids with
      | Asserted, [] ->
        if is_assumption p e.P.formula then
          let result = lifted p name e.P.formula [] true in
          result, seen, emit p result "tautology" [] lines
        else
          let index = T.position e.P.formula p.document.assertions 0 in
          let result = lifted p ("a" ^ string_of_int index) e.P.formula [] false in
          result, seen, lines
      | Hypothesis, [] ->
        let _literal = ground_literal p.document e.P.formula in
        let result = lifted p name e.P.formula [e.P.formula] false in
        result, seen, emit p result "tautology" [] lines
      | LemmaRule, [source] ->
        let parent, seen, lines = visit (fuel - 1) p source seen lines in
        let premise = T.entry_at source p.document.entries in
        let body = T.literals true premise.P.formula in
        if body <> [] then unsupported "a learned clause has a nonempty premise"
        else
          (* Local discharge must not discharge the designated input assumption. *)
          let hyps = remaining_hypotheses parent.hypotheses e.P.formula in
          let result, lines = finish p id e.P.formula hyps parent.uses_goal parent lines in
          result, seen, lines
      | ModusPonens, [source; equality]
      | ObservationalMP, [source; equality] ->
        let premise = T.entry_at source p.document.entries in
        let parent, seen, lines = visit (fuel - 1) p source seen lines in
        if T.same_clause premise.P.formula e.P.formula then
          if Quantifier? premise.P.formula && not (Quantifier? e.P.formula) then
            let result = lifted p name e.P.formula parent.hypotheses parent.uses_goal in
            result, seen, emit p result "instantiate" [parent.name] lines
          else parent, seen, lines
        else if T.equality_reduction premise.P.formula e.P.formula then
          let result = lifted p name e.P.formula parent.hypotheses parent.uses_goal in
          result, seen, emit p result "equality_resolution" [parent.name] lines
        else
          let equations, seen, lines = rewrites (fuel - 1) p equality seen lines in
          if equations = [] then unsupported "modus ponens has no supported term rewrites"
          else
            let hyps = L.fold_left (fun hs eq -> add_hypotheses eq.hypotheses hs)
                                  parent.hypotheses equations in
            let uses_goal =
              parent.uses_goal || not (L.for_all (fun eq -> not eq.uses_goal) equations) in
            let result = lifted p name e.P.formula hyps uses_goal in
            if parent.scope = result.scope && subset parent.values result.values then
              let result, lines = finish p id e.P.formula hyps uses_goal parent lines in
              result, seen, lines
            else
              let parents = parent.name :: L.map (fun eq -> eq.name) equations in
              result, seen, emit p result "forward_rewriting" parents lines
      | UnitResolution, first :: rest ->
        let inst = T.quantified_instance (fuel - 1) p.document first in
        let parent, remaining, seen, lines = match inst with
          | None ->
            let parent, seen, lines = visit (fuel - 1) p first seen lines in
            parent, rest, seen, lines
          | Some (q, body) ->
            let source, remaining = T.quantified_parent p.document q rest [] in
            let parent, seen, lines = visit (fuel - 1) p source seen lines in
            let result = lifted p (name ^ "_inst") body parent.hypotheses parent.uses_goal in
            let lines = emit p result "instantiate" [parent.name] lines in
            result, remaining, seen, lines in
        let result, seen, lines =
          resolve_units (fuel - 1) p name 0 parent remaining seen lines in
        let result, lines =
          finish p id e.P.formula result.hypotheses result.uses_goal result lines in
        result, seen, lines
      | Reflexivity, []
      | Symmetry, [_]
      | Transitivity, [_; _]
      | Congruence, _ ->
        let left, right = match T.equation e.P.formula with
          | Some pair -> pair
          | None -> unsupported "expected a ground equality conclusion" in
        let _left = T.term p.document [] left in
        let _right = T.term p.document [] right in
        if left = right then
          let result = lifted p name e.P.formula [] false in
          result, seen, emit p result "reflexivity" [] lines
        else
          let parents, seen, lines = visits (fuel - 1) p e.P.premise_ids seen lines in
          let hyps = L.fold_left (fun hs parent -> add_hypotheses parent.hypotheses hs) [] parents in
          let uses_goal = not (L.for_all (fun parent -> not parent.uses_goal) parents) in
          let result = lifted p name e.P.formula hyps uses_goal in
          let rule = if e.P.rule = Symmetry then "symmetry"
                     else if e.P.rule = Congruence then "congruence" else "superposition" in
          result, seen, emit p result rule (L.map (fun parent -> parent.name) parents) lines
      | _ -> unsupported ("unsupported rule at proof entry " ^ string_of_int id)
    in
    result, index_put seen id result, lines

and resolve_units (fuel:nat) (p:problem) (name:string) (step:nat) (current:derived)
                  (ids:list int) (seen:index_tree derived) (lines:list string)
  : ML (derived & index_tree derived & list string) =
  match ids with
  | [] -> current, seen, lines
  | id :: rest ->
    let e = T.entry_at id p.document.entries in
    let pivot = ground_literal p.document e.P.formula in
    let unit, seen, lines = visit fuel p id seen lines in
    if current.scope <> [] || unit.scope <> [] || not (contains unit.values pivot)
    then unsupported "unsupported resolution scope or unit"
    else
      let hyps = add_hypotheses current.hypotheses unit.hypotheses in
      let uses_goal = current.uses_goal || unit.uses_goal in
      let result, lines =
        if contains current.values (complement pivot) then
          let values = union (remove (complement pivot) current.values) (remove pivot unit.values) in
          let result = {
            name = name ^ "_r" ^ string_of_int step; scope = []; values = values;
            hypotheses = hyps; uses_goal = uses_goal } in
          result, emit p result "resolution" [current.name; unit.name] lines
        else { current with hypotheses = hyps; uses_goal = uses_goal }, lines in
      resolve_units fuel p name (step + 1) result rest seen lines

and visits (fuel:nat) (p:problem) (ids:list int)
           (seen:index_tree derived) (lines:list string)
  : ML (list derived & index_tree derived & list string) =
  match ids with
  | [] -> [], seen, lines
  | id :: rest ->
    let head, seen, lines = visit fuel p id seen lines in
    let tail, seen, lines = visits fuel p rest seen lines in
    head :: tail, seen, lines

and rewrites (fuel:nat) (p:problem) (id:int)
             (seen:index_tree derived) (lines:list string)
  : ML (list derived & index_tree derived & list string) =
  if fuel = 0 then unsupported "cyclic or oversized equality proof"
  else
    let e = T.entry_at id p.document.entries in
    match T.equation e.P.formula with
    | Some (a, b) ->
      if get_sort a <> bool_sort then
        let result, seen, lines = visit fuel p id seen lines in
        [result], seen, lines
      else if T.same_clause a b || T.equality_reduction a b then [], seen, lines
      else
        (match e.P.rule with
         | IffTrue | IffFalse ->
           visits (fuel - 1) p e.P.premise_ids seen lines
         | Congruence | Symmetry | Transitivity | TransitivityPath | IffObservational ->
           rewrite_arguments (fuel - 1) p e.P.premise_ids seen lines
         | _ -> unsupported ("unsupported Boolean rewrite at proof entry " ^ string_of_int id))
    | None -> unsupported "expected an equality proof for predicate rewriting"

and rewrite_arguments (fuel:nat) (p:problem) (ids:list int)
                      (seen:index_tree derived) (lines:list string)
  : ML (list derived & index_tree derived & list string) =
  match ids with
  | [] -> [], seen, lines
  | id :: rest ->
    let head, seen, lines = rewrites fuel p id seen lines in
    let tail, seen, lines = rewrite_arguments fuel p rest seen lines in
    L.append head tail, seen, lines

let rec inputs (p:problem) (assertions:list expr) (index:nat) : ML (list string) =
  match assertions with
  | [] -> []
  | e :: rest ->
    let line =
      if is_assumption p e then ""
      else
        let scope, body = T.universal_scope [] e in
        let values = T.literals true body in
        let formula = T.render_clause p.document scope values in
        T.keyword p.document ^ "(a" ^ string_of_int index ^ ",axiom,(" ^ formula ^ ")).\n" in
    let rest = inputs p rest (index + 1) in
    line :: rest

let export (doc:P.document) : ML string =
  match L.rev doc.assertions with
  | [] -> unsupported "a designated negated-goal assertion is required"
  | assumption :: _ ->
    let value = ground_literal doc assumption in
    let _, atom = value in
    let constant = match atom with
      | App d [] -> d.interp = Some op_true || d.interp = Some op_false
      | _ -> false in
    if constant
    then unsupported "the last assertion must be a nonconstant ground literal"
    else
      let p = { document = doc; goal = complement value } in
      let root = T.entry_at doc.root doc.entries in
      let body = T.literals true root.P.formula in
      if body <> [] then unsupported "the root is not the empty clause"
      else
        let axioms = inputs p doc.assertions 0 in
        let result, _, lines = visit (L.length doc.entries + 1) p doc.root Empty [] in
        if result.hypotheses <> [] || result.scope <> [] || not (subset result.values [p.goal])
        then unsupported "the root has undischarged assumptions"
        else
          let formula = T.render_clause doc [] [p.goal] in
          let rule = if result.values = [] then "weakening" else "reiteration" in
          let conclusion = T.keyword doc ^ "(goal_1,theorem,(" ^ formula ^
            "),inference(" ^ rule ^ ",[status(thm)],[" ^ result.name ^ "])).\n" in
          let types = if T.typed doc then
            let sorts = T.sort_declarations doc (T.type_sorts doc) 0 in
            let symbols = T.symbol_declarations doc doc.declarations 0 in
            sorts ^ symbols
            else "" in
          "% Native direct proof; the last input assertion is discharged, not an axiom.\n" ^
          types ^ T.join "" axioms ^ T.join "" (L.rev lines) ^ conclusion
