module Z3Tptp

open FStar.All
open Z3AstTheory
open Z3ValueTheory
open Z3UnifiedProof
open Z3ProofIndex
module P = Z3ProofDocument
module N = Z3Native
module L = FStar.List.Tot

(* This is an optional presentation exporter, not a proof-checking rule. *)
let unsupported (#a:Type) (message:string) : ML a =
  N.fail ("TSTP export: " ^ message)

let rec position (#a:eqtype) (value:a) (values:list a) (index:nat) : ML nat =
  match values with
  | [] -> unsupported "reference is absent from the checked document"
  | x :: rest -> if x = value then index else position value rest (index + 1)

let rec join (separator:string) (values:list string) : Tot string (decreases values) =
  match values with
  | [] -> ""
  | [x] -> x
  | x :: rest -> x ^ separator ^ join separator rest

let digit (c:FStar.Char.char) : bool =
  let n = FStar.Char.int_of_char c in
  48 <= n && n <= 57

let rec native_name_suffix (cs:list FStar.Char.char)
  : Tot (option string) (decreases cs) =
  match cs with
  | ':' :: rest -> Some (FStar.String.string_of_list rest)
  | c :: rest -> if digit c then native_name_suffix rest else None
  | [] -> None

let source_name (d:func_decl) : string =
  (* Native opaque identities are decl!<id>:<source-name>. *)
  match FStar.String.list_of_string d.decl_name with
  | 'd' :: 'e' :: 'c' :: 'l' :: '!' :: c :: rest ->
    if digit c then
      (match native_name_suffix rest with
       | Some name -> name
       | None -> d.decl_name)
    else d.decl_name
  | _ -> d.decl_name

let lower (c:FStar.Char.char) : bool =
  let n = FStar.Char.int_of_char c in
  97 <= n && n <= 122

let plain_word (name:string) : bool =
  match FStar.String.list_of_string name with
  | [] -> false
  | c :: rest ->
    lower c && L.for_all (fun c ->
      let n = FStar.Char.int_of_char c in
      lower c || (65 <= n && n <= 90) || digit c || c = '_') rest

let source_sort_name (s:sort) : option string =
  match s with
  | BaseSort name ->
    Some (match FStar.String.list_of_string name with
    | 's' :: 'o' :: 'r' :: 't' :: '!' :: c :: rest ->
      if digit c then
        (match native_name_suffix rest with Some name -> name | None -> name)
      else name
    | _ -> name)
  | _ -> None

let rec escape_atom (cs:list FStar.Char.char)
  : Tot (list FStar.Char.char) (decreases cs) =
  match cs with
  | [] -> []
  | c :: rest ->
    if c = '\'' || c = '\\' then '\\' :: c :: escape_atom rest
    else c :: escape_atom rest

let sort_atom (name:string) : option string =
  if plain_word name then Some name
  else
    let cs = FStar.String.list_of_string name in
    if cs <> [] && L.for_all (fun c ->
      let n = FStar.Char.int_of_char c in 32 <= n && n <= 126) cs
    then Some ("'" ^ FStar.String.string_of_list (escape_atom cs) ^ "'")
    else None

let rec bound_sorts (e:expr) : Tot (list sort) (decreases e) =
  match e with
  | Quantifier _ bs _ body -> L.append bs (bound_sorts body)
  | _ -> []

let type_sorts (doc:P.document) : list sort =
  let add sorts s = if s = bool_sort || L.mem s sorts then sorts else s :: sorts in
  let sorts = L.fold_left (fun sorts d ->
    L.fold_left add (add sorts d.range) d.domain) [] doc.declarations in
  L.fold_left (fun sorts e -> L.fold_left add sorts (bound_sorts e)) sorts doc.assertions

let rec fresh_name (name:string) (doc:P.document) : ML string =
  if L.for_all (fun d -> source_name d <> name) doc.declarations &&
     L.for_all (fun s -> source_sort_name s <> Some name) (type_sorts doc)
  then name
  else fresh_name (name ^ "_") doc

let symbol (doc:P.document) (d:func_decl) : ML string =
  let index = position d doc.declarations 0 in
  let name = source_name d in
  if plain_word name &&
     L.for_all (fun other ->
       other = d || other.interp <> None || source_name other <> name) doc.declarations
  then name
  else fresh_name ("d" ^ string_of_int index) doc

let rec universal_scope (scope:list sort) (e:expr) : ML (list sort & expr) =
  match e with
  | Quantifier Forall_k bs s body ->
    if s <> bool_sort || not (L.for_all (fun b -> b <> bool_sort) bs)
    then unsupported "expected universal binders over non-Boolean sorts"
    else universal_scope (L.append (L.rev bs) scope) body
  | Quantifier _ _ _ _ -> unsupported "existentials and lambdas are not supported"
  | _ -> scope, e

let typed (doc:P.document) : bool =
  not (L.for_all (fun e -> not (Quantifier? e)) doc.assertions)

let type_name (doc:P.document) (s:sort) : ML string =
  if s = bool_sort then "$o"
  else
    let sorts = type_sorts doc in
    let name = match source_sort_name s with
      | Some name ->
        if L.for_all (fun other ->
             other = s || source_sort_name other <> Some name) sorts &&
           L.for_all (fun d -> source_name d <> name) doc.declarations
        then sort_atom name else None
      | None -> None in
    match name with
    | Some name -> name
    | None -> fresh_name ("s" ^ string_of_int (position s sorts 0)) doc

let rec type_names (doc:P.document) (ss:list sort) : ML (list string) =
  match ss with
  | [] -> []
  | s :: rest ->
    let name = type_name doc s in
    let rest = type_names doc rest in
    name :: rest

let rec sort_declarations (doc:P.document) (ss:list sort) (index:nat) : ML string =
  match ss with
  | [] -> ""
  | s :: rest ->
    let name = type_name doc s in
    let rest = sort_declarations doc rest (index + 1) in
    "tff(ts" ^ string_of_int index ^ ",type," ^ name ^ ":$tType).\n" ^ rest

let rec symbol_declarations (doc:P.document) (ds:list func_decl) (index:nat) : ML string =
  match ds with
  | [] -> ""
  | d :: rest ->
    let declaration =
      if d.interp <> None then ""
      else
        let name = symbol doc d in
        let domain = type_names doc d.domain in
        let range = type_name doc d.range in
        let signature = if domain = [] then range
                        else "(" ^ join " * " domain ^ ") > " ^ range in
        "tff(td" ^ string_of_int index ^ ",type," ^ name ^ ":" ^ signature ^ ").\n" in
    let rest = symbol_declarations doc rest (index + 1) in
    declaration ^ rest

let rec binders (doc:P.document) (ss:list sort) (index:nat) : ML (list string) =
  match ss with
  | [] -> []
  | s :: rest ->
    let name = type_name doc s in
    let binder = "X" ^ string_of_int index ^ ":" ^ name in
    let rest = binders doc rest (index + 1) in
    binder :: rest

let rec term (doc:P.document) (scope:list sort) (e:expr) : ML string =
  match e with
  | Var index s ->
    if index < L.length scope && L.index scope index = s && s <> bool_sort
    then "X" ^ string_of_int (L.length scope - 1 - index)
    else unsupported "free or incorrectly sorted variable"
  | App d args ->
    if d.interp <> None || d.range = BaseSort "Bool" ||
       not (L.for_all (fun s -> s <> BaseSort "Bool") d.domain)
    then unsupported "expected an uninterpreted, non-Boolean term"
    else application doc scope d args
  | _ -> unsupported "quantified terms and lambdas are not supported"

and application (doc:P.document) (scope:list sort) (d:func_decl) (args:list expr) : ML string =
  let name = symbol doc d in
  let args = terms doc scope args in
  if args = [] then name else name ^ "(" ^ join "," args ^ ")"

and terms (doc:P.document) (scope:list sort) (args:list expr) : ML (list string) =
  match args with
  | [] -> []
  | e :: rest ->
    let e = term doc scope e in
    let rest = terms doc scope rest in
    e :: rest

let atom (doc:P.document) (scope:list sort) (e:expr) : ML string =
  match e with
  | App d args ->
    if args = [] && d.interp = Some op_true then "$true"
    else if args = [] && d.interp = Some op_false then "$false"
    else if d.interp = Some op_eq then
      (match args with
       | [a; b] ->
         let a = term doc scope a in
         let b = term doc scope b in
         a ^ " = " ^ b
       | _ -> unsupported "malformed equality")
    else if d.interp = None && d.range = BaseSort "Bool" &&
            L.for_all (fun s -> s <> BaseSort "Bool") d.domain
    then application doc scope d args
    else unsupported "expected an uninterpreted predicate or term equality"
  | _ -> unsupported "expected an uninterpreted predicate or term equality"

type literal = bool & expr

let rec literals (positive:bool) (e:expr) : ML (list literal) =
  match e with
  | App d args ->
    if d.interp = Some op_not then
      (match args with
       | [a] -> literals (not positive) a
       | _ -> unsupported "malformed negation")
    else if (positive && d.interp = Some op_or) ||
            (not positive && d.interp = Some op_and)
    then literal_arguments positive args
    else if positive && d.interp = Some op_implies then
      (match args with
       | [a; b] ->
         let left = literals false a in
         let right = literals true b in
         L.append left right
       | _ -> unsupported "malformed implication")
    else if args = [] && ((positive && d.interp = Some op_false) ||
                         (not positive && d.interp = Some op_true))
    then []
    else [positive, e]
  | _ -> [positive, e]

and literal_arguments (positive:bool) (args:list expr) : ML (list literal) =
  match args with
  | [] -> []
  | e :: rest ->
    let head = literals positive e in
    let tail = literal_arguments positive rest in
    L.append head tail

let rec render_literals (doc:P.document) (scope:list sort) (values:list literal) : ML (list string) =
  match values with
  | [] -> []
  | (positive, e) :: rest ->
    let a = atom doc scope e in
    let a = if positive then "(" ^ a ^ ")" else "~(" ^ a ^ ")" in
    let rest = render_literals doc scope rest in
    a :: rest

let clause (doc:P.document) (e:expr) : ML string =
  let scope, body = universal_scope [] e in
  let values = literals true body in
  let positives = L.fold_left (fun n (positive, _) -> if positive then n + 1 else n) 0 values in
  if positives > 1 then unsupported "a clause is not Horn"
  else
    let rendered = render_literals doc scope values in
    let formula = if rendered = [] then "$false" else join " | " rendered in
    if scope = [] then formula
    else
      let variables = binders doc (L.rev scope) 0 in
      "![" ^ join "," variables ^ "]:(" ^ formula ^ ")"

let equation (e:expr) : option (expr & expr) =
  match e with
  | App d [a; b] ->
    if d.interp = Some op_eq || d.interp = Some op_oeq then Some (a, b) else None
  | _ -> None

let true_atom (e:expr) : bool =
  match e with
  | App d [] -> d.interp = Some op_true
  | App d [a; b] -> d.interp = Some op_eq && a = b && get_sort a <> bool_sort
  | _ -> false

let same_atom (a b:expr) : bool =
  a = b || (true_atom a && true_atom b) ||
           (match a, b, equation a, equation b with
            | App f _, App g _, Some (s, t), Some (u, v) ->
              f.interp = g.interp && s = v && t = u
            | _ -> false)

let same_literals (a b:list literal) : bool =
  let contained xs ys =
    L.for_all (fun (positive, e) ->
      not (L.for_all (fun (other, f) -> positive <> other || not (same_atom e f)) ys)) xs in
  contained a b && contained b a

let same_clause (a b:expr) : ML bool =
  let sa, ba = universal_scope [] a in
  let sb, bb = universal_scope [] b in
  let la = literals true ba in
  let lb = literals true bb in
  (sa = sb && same_literals la lb) ||
  ((Quantifier? a || Quantifier? b) && Z3QuantifierReduce.equivalent 64 a b)

let equality_reduction (a b:expr) : ML bool =
  let before = literals true a in
  let after = L.fold_left (fun kept (positive, e) ->
    let reflexive = match equation e with
      | Some (s, t) -> s = t && get_sort s <> bool_sort
      | None -> false in
    if not positive && reflexive then kept else (positive, e) :: kept) [] before in
  let target = literals true b in
  L.length after < L.length before && same_literals after target

let keyword (doc:P.document) : string = if typed doc then "tff" else "cnf"

let inference (doc:P.document) (name formula rule:string) (parents:list string) : string =
  keyword doc ^ "(" ^ name ^ ",plain,(" ^ formula ^
  "),inference(" ^ rule ^ ",[status(thm)],[" ^ join "," parents ^ "])).\n"

let rec entry_at (index:int) (entries:list P.entry) : ML P.entry =
  match entries with
  | [] -> unsupported "invalid proof entry reference"
  | e :: rest ->
    if index < 0 then unsupported "negative proof entry reference"
    else if index = 0 then e else entry_at (index - 1) rest

let rec inputs (doc:P.document) (assertions:list expr) (index:nat) : ML (list string) =
  match assertions with
  | [] -> []
  | e :: rest ->
    let formula = clause doc e in
    let line = keyword doc ^ "(a" ^ string_of_int index ^ ",axiom,(" ^ formula ^ ")).\n" in
    let rest = inputs doc rest (index + 1) in
    line :: rest

let rec quantified_instance (fuel:nat) (doc:P.document) (id:int)
  : ML (option (expr & expr)) =
  if fuel = 0 then unsupported "cyclic or oversized instantiation proof"
  else
    let e = entry_at id doc.entries in
    match e.P.rule, e.P.premise_ids with
    | QuantifierInstantiation args, [] ->
      if not (Z3QuantifierInstantiation.check args e.P.formula)
      then unsupported "invalid universal instantiation"
      else
        (match e.P.formula with
         | App _ [App _ [q]; inst] -> Some (q, inst)
         | _ -> unsupported "malformed universal instantiation")
    | ModusPonens, [source; _]
    | ObservationalMP, [source; _] ->
      let premise = entry_at source doc.entries in
      if same_clause premise.P.formula e.P.formula
      then quantified_instance (fuel - 1) doc source else None
    | _ -> None

let rec quantified_parent (doc:P.document) (q:expr) (ids before:list int)
  : ML (int & list int) =
  match ids with
  | [] -> unsupported "instantiation has no universal premise"
  | id :: rest ->
    let e = entry_at id doc.entries in
    if e.P.formula = q then id, L.append (L.rev before) rest
    else quantified_parent doc q rest (id :: before)

let rec visit (fuel:nat) (doc:P.document) (id:int)
              (seen:index_tree string) (lines:list string)
  : ML (string & index_tree string & list string) =
  if fuel = 0 then unsupported "cyclic or oversized proof"
  else if id < 0 then unsupported "negative proof entry reference"
  else match index_get seen id with
  | Some name -> name, seen, lines
  | None ->
    let e = entry_at id doc.entries in
    let name, seen, lines =
      match e.P.rule, e.P.premise_ids with
      | Asserted, [] ->
        let index = position e.P.formula doc.assertions 0 in
        "a" ^ string_of_int index, seen, lines
      | ModusPonens, [source; equality]
      | ObservationalMP, [source; equality] ->
        let premise = entry_at source doc.entries in
        if same_clause premise.P.formula e.P.formula
        then
          let parent, seen, lines = visit (fuel - 1) doc source seen lines in
          if Quantifier? premise.P.formula && not (Quantifier? e.P.formula) then
            let name = "p" ^ string_of_int id in
            let formula = clause doc e.P.formula in
            name, seen, inference doc name formula "instantiate" [parent] :: lines
          else parent, seen, lines
        else
          let parent, seen, lines = visit (fuel - 1) doc source seen lines in
          let formula = clause doc e.P.formula in
          let name = "p" ^ string_of_int id in
          if equality_reduction premise.P.formula e.P.formula then
            name, seen, inference doc name formula "equality_resolution" [parent] :: lines
          else
            let equations, seen, lines = rewrites (fuel - 1) doc equality seen lines in
            if equations = [] then unsupported "modus ponens has no supported term rewrites"
            else name, seen,
              inference doc name formula "forward_demodulation" (parent :: equations) :: lines
      | UnitResolution, first :: rest ->
        let inst = quantified_instance (fuel - 1) doc first in
        let parents, seen, lines = match inst with
          | None -> visits (fuel - 1) doc e.P.premise_ids seen lines
          | Some (q, body) ->
            let parent, remaining = quantified_parent doc q rest [] in
            let parent, seen, lines = visit (fuel - 1) doc parent seen lines in
            let name = "p" ^ string_of_int id ^ "_inst" in
            let formula = clause doc body in
            let lines = inference doc name formula "instantiate" [parent] :: lines in
            let parents, seen, lines = visits (fuel - 1) doc remaining seen lines in
            name :: parents, seen, lines in
        (match parents with
         | [parent] ->
           (match inst with
            | Some (_, body) ->
              if same_clause body e.P.formula then parent, seen, lines
              else unsupported "unexpected universal-instantiation conclusion"
            | None ->
              let formula = clause doc e.P.formula in
              let name = "p" ^ string_of_int id in
              name, seen, inference doc name formula "resolution" [parent] :: lines)
         | _ ->
           let formula = clause doc e.P.formula in
           let name = "p" ^ string_of_int id in
           name, seen, inference doc name formula "resolution" parents :: lines)
      | Reflexivity, []
      | Symmetry, [_]
      | Transitivity, [_; _]
      | Congruence, _ ->
        let left, right = match equation e.P.formula with
          | Some pair -> pair
          | None -> unsupported "expected an equality conclusion" in
        let identical = left = right in
        let left = term doc [] left in
        let formula = clause doc e.P.formula in
        let name = "p" ^ string_of_int id in
        if e.P.rule = Reflexivity || identical then
          name, seen, inference doc name formula "reflexivity" [] :: lines
        else if e.P.rule = Congruence then
          let parents, seen, lines = visits (fuel - 1) doc e.P.premise_ids seen lines in
          let reflexive = name ^ "_refl" in
          let lines = inference doc reflexive (left ^ " = " ^ left) "reflexivity" [] :: lines in
          name, seen, inference doc name formula "rewriting" (reflexive :: parents) :: lines
        else
          let parents, seen, lines = visits (fuel - 1) doc e.P.premise_ids seen lines in
          let rule = if e.P.rule = Symmetry then "symmetry" else "superposition" in
          name, seen, inference doc name formula rule parents :: lines
      | _ -> unsupported ("unsupported rule at proof entry " ^ string_of_int id)
    in
    name, index_put seen id name, lines

and visits (fuel:nat) (doc:P.document) (ids:list int)
           (seen:index_tree string) (lines:list string)
  : ML (list string & index_tree string & list string) =
  match ids with
  | [] -> [], seen, lines
  | id :: rest ->
    let name, seen, lines = visit fuel doc id seen lines in
    let names, seen, lines = visits fuel doc rest seen lines in
    name :: names, seen, lines

and rewrites (fuel:nat) (doc:P.document) (id:int)
             (seen:index_tree string) (lines:list string)
  : ML (list string & index_tree string & list string) =
  if fuel = 0 then unsupported "cyclic or oversized equality proof"
  else
    let e = entry_at id doc.entries in
    match equation e.P.formula with
    | Some (a, b) ->
      if get_sort a <> bool_sort then
        let name, seen, lines = visit fuel doc id seen lines in
        [name], seen, lines
      else if same_clause a b || equality_reduction a b then [], seen, lines
      else
        (match e.P.rule with
         | Congruence | Symmetry | Transitivity | TransitivityPath | IffObservational ->
           rewrite_arguments (fuel - 1) doc e.P.premise_ids seen lines
         | _ -> unsupported ("unsupported Boolean rewrite at proof entry " ^ string_of_int id))
    | None -> unsupported "expected an equality proof for predicate rewriting"

and rewrite_arguments (fuel:nat) (doc:P.document) (ids:list int)
                      (seen:index_tree string) (lines:list string)
  : ML (list string & index_tree string & list string) =
  match ids with
  | [] -> [], seen, lines
  | id :: rest ->
    let head, seen, lines = rewrites fuel doc id seen lines in
    let tail, seen, lines = rewrite_arguments fuel doc rest seen lines in
    L.append head tail, seen, lines

let export (doc:P.document) : ML string =
  let root = entry_at doc.root doc.entries in
  let root_clause = literals true root.P.formula in
  if root_clause <> [] then unsupported "the root is not the empty clause"
  else
    let axioms = inputs doc doc.assertions 0 in
    let _, _, lines = visit (L.length doc.entries + 1) doc doc.root Empty [] in
    if lines = [] then unsupported "the refutation has no supported inference steps"
    else
    let types = if typed doc then
      let sorts = sort_declarations doc (type_sorts doc) 0 in
      let symbols = symbol_declarations doc doc.declarations 0 in
      sorts ^ symbols
      else "" in
    "% Horn refutation; declaration names are preserved where unambiguous.\n" ^ types ^
    join "" axioms ^ join "" (L.rev lines)
