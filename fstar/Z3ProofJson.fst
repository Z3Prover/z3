(*
   Z3ProofJson.fst

   A from-scratch JSON reader + decoder for `Z3ProofTheory.fst`'s
   `proof` type (and the `sort`/`func_decl`/`expr` types it is built
   from, `Z3AstTheory.fst`). This is the data-side half of moving the
   proof-checking harness from "regenerate and recompile a bespoke
   `.fst` module, with the proof literally spelled out as F* source,
   for every single benchmark" to "compile the checker once; feed it
   a JSON *string* describing each new proof".

   Motivation / what problem this solves
   --------------------------------------
   `tools/extract_z3_proof.py`'s original `generate()` wrote one
   `.fst` file per benchmark in which every sort/decl/expr/proof node
   was a top-level `let` binding of literal F* syntax (`e_17 : expr =
   App fd_3 [e_12; e_16]`, etc.). Every such file pulls in the full
   dependency stack (`Z3AstTheory`/`Z3ValueTheory`/`Z3ProofTheory`/
   `Z3InterpretedProofChecker`/`Z3PatternMatchedProofChecker`/
   `Z3PulseProofChecker`) and `fstar.exe` re-elaborates/re-verifies
   *all* of it (modulo `.checked`-file caching of the *unchanged*
   dependencies) plus however many hundred `let`-bindings the proof
   itself needed, every single run.

   With this module, the dependency stack above is exactly what it
   was -- unchanged, and still separately audited by its own reports
   -- but it is compiled *once* (`.checked` files for it never need to
   change from one proof to the next). Each new proof becomes a tiny,
   uniform "instance" file of the shape

       let proof_json : string = "{...the whole proof, as JSON...}"
       let _ = assert_norm (check_proof_json_ok proof_json)

   i.e. the only per-proof artifact F* has to elaborate afresh is one
   string literal plus one call into already-checked code -- the
   proof *checker* itself is never recompiled, only *applied*, no
   differently than how a compiled program is "applied" to new input
   data in any other language.

   JSON subset supported
   ----------------------
   This is not a general-purpose JSON library: it supports exactly the
   subset this project's proof-certificate schema below needs --
   objects, arrays, (non-negative-or-negative) decimal integers,
   double-quoted strings (with `\"`/`\\` escapes only, no unicode
   escapes), and the `null` literal -- and nothing else (no floating
   point, no `true`/`false`, no multi-byte/unicode decoding). Anything
   outside that subset simply fails to parse (`None`), which is a safe
   (fail-closed, never "succeeds with the wrong meaning") default.

   Proof-document schema (structure sharing via index arrays)
   ------------------------------------------------------------
   The document is one JSON object:

     { "sorts": [...], "decls": [...], "exprs": [...], "proofs": [...],
       "root": <int>, "unmatched_count": <int> }

   Each of `sorts`/`decls`/`exprs`/`proofs` is a JSON *array*; the
   i-th element (0-based) is "node i", and every reference to another
   node is just that node's integer index into the relevant array.
   Crucially, **a node is listed exactly once, in its array, no matter
   how many other nodes refer to it** -- this is the "structure
   sharing" a hash-consed proof DAG actually has (the same sub-`expr`
   or sub-`proof` can be, and typically is, the premise/argument of
   several different nodes at once); decoding below rebuilds that
   sharing faithfully (a shared JSON index decodes to the *same* F*
   value, by construction of the incremental "already-decoded prefix"
   accumulator each decoder threads through), unlike the old
   `.fst`-generation path, which incidentally also shared via F*
   `let`-bindings but could only do so by naming every node, one `let`
   per node, in a fixed file.

   Per-array element shapes:

     sorts[i]  = {"kind":"base","name":<string>}
               | {"kind":"array","dom":[sort idx, ...],"rng":<sort idx>}

     decls[i]  = {"name":<string>, "domain":[sort idx,...], "range":<sort idx>,
                  "interp": <op tag string> | null,   (* optional, default null *)
                  "int_params": [<int>, ...] }         (* optional, default [] *)

       <op tag string> is one of this project's named interpreted
       operators (`Z3ValueTheory.fst`'s `op_not`/`op_plus`/
       `op_select`/`op_store`/`op_bvand`/`op_concat`/`op_eq`/
       `op_true`/`op_false`/`op_num_int`/`op_num_bv`/`op_seq_unit`/
       `op_and`/`op_or`/`op_implies`), by name; any other string fails
       to parse (fail-closed: a typo or future operator never silently
       becomes "uninterpreted").

     exprs[i]  = {"kind":"var","idx":<nat>,"sort":<sort idx>}
               | {"kind":"app","decl":<decl idx>,"args":[expr idx,...]}
               | {"kind":"quant","qk":"forall"|"exists"|"lambda",
                  "bound_sorts":[sort idx,...],"qsort":<sort idx>,
                  "body":<expr idx>}

     proofs[i] = {"kind":"refl","e":<expr idx>}
               | {"kind":"sym","p":<proof idx>}
               | {"kind":"trans","p1":<proof idx>,"p2":<proof idx>}
               | {"kind":"congr","decl":<decl idx>,
                  "args1":[expr idx,...],"args2":[expr idx,...],
                  "prfs":[proof idx,...]}
               | {"kind":"rewrite","s":<expr idx>,"t":<expr idx>}
               | {"kind":"quant_intro","qk":"forall"|"exists",
                  "bound_sorts":[sort idx,...],"p":<proof idx>}

   Every index a node contains must refer to an *earlier* element of
   the relevant array (`sorts`/`decls`/`exprs` indices used inside an
   `exprs[i]` node must be `< i`'s own position is not required --
   only that the referenced array's prefix already decoded is long
   enough; in practice `tools/extract_z3_proof.py` emits every array
   in a topological, "dependencies first" order, exactly as it always
   has for its F*-source `let`-bindings). This acyclicity requirement
   is exactly what lets decoding below be a simple linear left-to-right
   fold with no fixpoint/laziness machinery.
*)
module Z3ProofJson

open Z3AstTheory
open Z3ProofTheory
open Z3ValueTheory
module L = FStar.List.Tot

(* ----------------------------------------------------------------- *)
(* 1. A minimal JSON value type                                       *)
(* ----------------------------------------------------------------- *)

noeq
type json =
  | JNull : json
  | JInt  : int -> json
  | JBool : bool -> json
  | JStr  : string -> json
  | JArr  : list json -> json
  | JObj  : list (string & json) -> json

(* ----------------------------------------------------------------- *)
(* 2. The parser: fuel-bounded recursive descent over `list FStar.Char.char`     *)
(* ----------------------------------------------------------------- *)

(* A plain structural-recursion termination proof over `list FStar.Char.char`
   for a mutually-recursive parser (value / string / array / object)
   that also needs to skip whitespace between tokens is more SMT work
   than it is worth here; an explicit fuel counter, decremented by
   exactly one on every recursive call, makes termination trivial
   (`decreases fuel`, a bare `nat`) at the cost of requiring the
   caller to supply enough fuel. `default_fuel` below supplies a
   generous, always-sufficient bound; running out of fuel before a
   well-formed document is fully consumed can only make parsing
   (safely) fail, never succeed with a wrong answer. *)

let is_ws (c:FStar.Char.char) : bool = c = ' ' || c = '\t' || c = '\n' || c = '\r'

let rec skip_ws (cs:list FStar.Char.char) : Tot (list FStar.Char.char) (decreases cs) =
  match cs with
  | c :: cs' -> if is_ws c then skip_ws cs' else cs
  | [] -> []

let is_digit (c:FStar.Char.char) : bool =
  let v = FStar.UInt32.v (FStar.Char.u32_of_char c) in
  v >= 48 && v <= 57

let digit_val (c:FStar.Char.char) : int = FStar.UInt32.v (FStar.Char.u32_of_char c) - 48

let rec take_digits (cs:list FStar.Char.char) (acc:int) : Tot (int & list FStar.Char.char) (decreases cs) =
  match cs with
  | c :: cs' -> if is_digit c then take_digits cs' (acc * 10 + digit_val c) else (acc, cs)
  | [] -> (acc, cs)

let parse_number (cs:list FStar.Char.char) : option (json & list FStar.Char.char) =
  match cs with
  | '-' :: c :: cs' ->
    if is_digit c then (let (n, rest) = take_digits (c :: cs') 0 in Some (JInt (- n), rest)) else None
  | c :: _ -> if is_digit c then (let (n, rest) = take_digits cs 0 in Some (JInt n, rest)) else None
  | [] -> None

let string_of_chars (cs:list FStar.Char.char) : string =
  FStar.String.string_of_list cs

let rec parse_value (fuel:nat) (cs:list FStar.Char.char) : Tot (option (json & list FStar.Char.char)) (decreases fuel) =
  if fuel = 0 then None else
  match skip_ws cs with
  | [] -> None
  | '"' :: cs' ->
    (match take_string (fuel - 1) cs' [] with
     | Some (s, rest) -> Some (JStr s, rest)
     | None -> None)
  | '[' :: cs' ->
    (match parse_array (fuel - 1) (skip_ws cs') with
     | Some (l, rest) -> Some (JArr l, rest)
     | None -> None)
  | '{' :: cs' ->
    (match parse_object (fuel - 1) (skip_ws cs') with
     | Some (kvs, rest) -> Some (JObj kvs, rest)
     | None -> None)
  | 'n' :: 'u' :: 'l' :: 'l' :: cs' -> Some (JNull, cs')
  | 't' :: 'r' :: 'u' :: 'e' :: cs' -> Some (JBool true, cs')
  | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: cs' -> Some (JBool false, cs')
  | cs' -> parse_number cs'

and take_string (fuel:nat) (cs:list FStar.Char.char) (acc:list FStar.Char.char) : Tot (option (string & list FStar.Char.char)) (decreases fuel) =
  if fuel = 0 then None else
  match cs with
  | [] -> None
  | '"' :: cs' -> Some (string_of_chars (L.rev acc), cs')
  | '\\' :: c :: cs' -> take_string (fuel - 1) cs' (c :: acc)
  | c :: cs' -> take_string (fuel - 1) cs' (c :: acc)

and parse_array (fuel:nat) (cs:list FStar.Char.char) : Tot (option (list json & list FStar.Char.char)) (decreases fuel) =
  if fuel = 0 then None else
  match cs with
  | ']' :: cs' -> Some ([], cs')
  | _ ->
    (match parse_value (fuel - 1) cs with
     | None -> None
     | Some (v, rest) ->
       (match skip_ws rest with
        | ',' :: rest' ->
          (match parse_array (fuel - 1) (skip_ws rest') with
           | Some (vs, rest'') -> Some (v :: vs, rest'')
           | None -> None)
        | ']' :: rest' -> Some ([v], rest')
        | _ -> None))

and parse_object (fuel:nat) (cs:list FStar.Char.char) : Tot (option (list (string & json) & list FStar.Char.char)) (decreases fuel) =
  if fuel = 0 then None else
  match cs with
  | '}' :: cs' -> Some ([], cs')
  | '"' :: cs' ->
    (match take_string (fuel - 1) cs' [] with
     | None -> None
     | Some (key, rest) ->
       (match skip_ws rest with
        | ':' :: rest' ->
          (match parse_value (fuel - 1) (skip_ws rest') with
           | None -> None
           | Some (v, rest2) ->
             (match skip_ws rest2 with
              | ',' :: rest3 ->
                (match parse_object (fuel - 1) (skip_ws rest3) with
                 | Some (kvs, rest4) -> Some ((key, v) :: kvs, rest4)
                 | None -> None)
              | '}' :: rest3 -> Some ([(key, v)], rest3)
              | _ -> None))
        | _ -> None))
  | _ -> None

(* Generous enough for any realistic proof document: every byte of
   input costs at most one unit of fuel at every parser level it
   passes through (the worst case, `take_string`, spends exactly one
   fuel unit per character); `4 *` covers whitespace-skipping/array
   and object nesting overhead with margin to spare. *)
let default_fuel (s:string) : nat = 4 * FStar.String.length s + 64

let parse_json (s:string) : option json =
  match parse_value (default_fuel s) (FStar.String.list_of_string s) with
  | Some (j, rest) -> (match skip_ws rest with [] -> Some j | _ -> None)
  | None -> None

(* ----------------------------------------------------------------- *)
(* 3. Small option-monad plumbing                                     *)
(* ----------------------------------------------------------------- *)

let bind_opt (#a #b:Type) (x:option a) (f:a -> option b) : option b =
  match x with
  | Some y -> f y
  | None -> None

let ( >>= ) = bind_opt

let rec opt_map (#a #b:Type) (f:a -> option b) (l:list a) : Tot (option (list b)) (decreases l) =
  match l with
  | [] -> Some []
  | x :: xs ->
    (match f x, opt_map f xs with
     | Some y, Some ys -> Some (y :: ys)
     | _, _ -> None)

let rec nth_opt (#a:Type) (l:list a) (i:int) : Tot (option a) (decreases l) =
  match l with
  | [] -> None
  | x :: xs -> if i = 0 then Some x else if i < 0 then None else nth_opt xs (i - 1)

(* Persistent numeric caches keep proof identity explicit and permit
   logarithmic reference lookup without hashing recursive proof terms. *)
noeq
type index_tree (a:Type) =
  | Empty : index_tree a
  | Branch : option a -> index_tree a -> index_tree a -> index_tree a

let rec index_get (#a:Type) (tree:index_tree a) (key:nat)
  : Tot (option a) (decreases key) =
  match tree with
  | Empty -> None
  | Branch value left right ->
    if key = 0 then value
    else if key % 2 = 1 then index_get left ((key - 1) / 2)
    else index_get right ((key - 1) / 2)

let rec index_put (#a:Type) (tree:index_tree a) (key:nat) (value:a)
  : Tot (index_tree a) (decreases key) =
  let old, left, right =
    match tree with
    | Empty -> None, Empty, Empty
    | Branch old left right -> old, left, right
  in
  if key = 0 then Branch (Some value) left right
  else if key % 2 = 1 then Branch old (index_put left ((key - 1) / 2) value) right
  else Branch old left (index_put right ((key - 1) / 2) value)

let index_find (#a:Type) (tree:index_tree a) (key:int) : option a =
  if key < 0 then None else index_get tree key

let rec lemma_index_put (#a:Type) (tree:index_tree a) (key:nat) (value:a) (query:nat)
  : Lemma (index_get (index_put tree key value) query ==
           (if query = key then Some value else index_get tree query))
          (decreases key) =
  if key = 0 || query = 0 then ()
  else
    let left, right =
      match tree with Empty -> Empty, Empty | Branch _ left right -> left, right
    in
    if key % 2 = query % 2 then
      lemma_index_put (if key % 2 = 1 then left else right)
        ((key - 1) / 2) value ((query - 1) / 2)

let rec json_field (fields:list (string & json)) (name:string) : Tot (option json) (decreases fields) =
  match fields with
  | [] -> None
  | (k, v) :: rest -> if k = name then Some v else json_field rest name

let json_obj (j:json) : option (list (string & json)) = match j with JObj l -> Some l | _ -> None
let json_arr (j:json) : option (list json) = match j with JArr l -> Some l | _ -> None
let json_int (j:json) : option int = match j with JInt n -> Some n | _ -> None
let json_str (j:json) : option string = match j with JStr s -> Some s | _ -> None

(* ----------------------------------------------------------------- *)
(* 4. Decoding sorts/decls/exprs/proofs, incrementally, with sharing  *)
(* ----------------------------------------------------------------- *)

let decode_sort_one (prev:list sort) (j:json) : option sort =
  json_obj j >>= (fun fields ->
  json_field fields "kind" >>= json_str >>= (fun kind ->
  if kind = "base" then
    json_field fields "name" >>= json_str >>= (fun name -> Some (BaseSort name))
  else if kind = "array" then
    json_field fields "dom" >>= json_arr >>= opt_map json_int >>= opt_map (nth_opt prev) >>= (fun doms ->
    json_field fields "rng" >>= json_int >>= nth_opt prev >>= (fun rng ->
    Some (ArraySort doms rng)))
  else None))

let rec decode_sorts (acc:list sort) (js:list json) : Tot (option (list sort)) (decreases js) =
  match js with
  | [] -> Some acc
  | j :: js' -> decode_sort_one acc j >>= (fun s -> decode_sorts (acc @ [s]) js')

let decl_kind_of_tag (tag:string) : option decl_kind =
  if tag = "op_not" then Some op_not
  else if tag = "op_plus" then Some op_plus
  else if tag = "op_mul" then Some op_mul
  else if tag = "op_select" then Some op_select
  else if tag = "op_store" then Some op_store
  else if tag = "op_array_ext" then Some op_array_ext
  else if tag = "op_bvand" then Some op_bvand
  else if tag = "op_concat" then Some op_concat
  else if tag = "op_eq" then Some op_eq
  else if tag = "op_true" then Some op_true
  else if tag = "op_false" then Some op_false
  else if tag = "op_num_int" then Some op_num_int
  else if tag = "op_num_bv" then Some op_num_bv
  else if tag = "op_seq_unit" then Some op_seq_unit
  else if tag = "op_and" then Some op_and
  else if tag = "op_or" then Some op_or
  else if tag = "op_implies" then Some op_implies
  else if tag = "op_oeq" then Some op_oeq
  else None

let decode_interp (fields:list (string & json)) : option (option decl_kind) =
  match json_field fields "interp" with
  | None -> Some None
  | Some JNull -> Some None
  | Some (JStr tag) -> (match decl_kind_of_tag tag with Some k -> Some (Some k) | None -> None)
  | Some _ -> None

let decode_int_params (fields:list (string & json)) : option (list int) =
  match json_field fields "int_params" with
  | None -> Some []
  | Some (JArr ps) -> opt_map json_int ps
  | Some _ -> None

let decode_decl_one (sorts:list sort) (j:json) : option func_decl =
  json_obj j >>= (fun fields ->
  json_field fields "name" >>= json_str >>= (fun name ->
  json_field fields "domain" >>= json_arr >>= opt_map json_int >>= opt_map (nth_opt sorts) >>= (fun doms ->
  json_field fields "range" >>= json_int >>= nth_opt sorts >>= (fun rng ->
  decode_interp fields >>= (fun interp ->
  decode_int_params fields >>= (fun int_params ->
  Some { decl_name = name; domain = doms; range = rng; interp = interp; int_params = int_params }))))))

let rec decode_decls (sorts:list sort) (acc:list func_decl) (js:list json) : Tot (option (list func_decl)) (decreases js) =
  match js with
  | [] -> Some acc
  | j :: js' -> decode_decl_one sorts j >>= (fun d -> decode_decls sorts (acc @ [d]) js')

let quantifier_kind_of_tag (s:string) : option quantifier_kind =
  if s = "forall" then Some Forall_k
  else if s = "exists" then Some Exists_k
  else if s = "lambda" then Some Lambda_k
  else None

let decode_expr_with (sorts:list sort) (decls:list func_decl)
                     (previous:int -> option expr) (j:json) : option expr =
  json_obj j >>= (fun fields ->
  json_field fields "kind" >>= json_str >>= (fun kind ->
  if kind = "var" then
    json_field fields "idx" >>= json_int >>= (fun idx ->
    json_field fields "sort" >>= json_int >>= nth_opt sorts >>= (fun s ->
    if idx >= 0 then Some (Var idx s) else None))
  else if kind = "app" then
    json_field fields "decl" >>= json_int >>= nth_opt decls >>= (fun d ->
    json_field fields "args" >>= json_arr >>= opt_map json_int >>= opt_map previous >>= (fun args ->
    Some (App d args)))
  else if kind = "quant" then
    json_field fields "qk" >>= json_str >>= quantifier_kind_of_tag >>= (fun qk ->
    json_field fields "bound_sorts" >>= json_arr >>= opt_map json_int >>= opt_map (nth_opt sorts) >>= (fun bs ->
    json_field fields "qsort" >>= json_int >>= nth_opt sorts >>= (fun qs ->
    json_field fields "body" >>= json_int >>= previous >>= (fun body ->
    Some (Quantifier qk bs qs body)))))
  else None))

let decode_expr_one (sorts:list sort) (decls:list func_decl) (prev:list expr) (j:json) : option expr =
  decode_expr_with sorts decls (nth_opt prev) j

let rec decode_exprs (sorts:list sort) (decls:list func_decl) (acc:list expr) (js:list json)
  : Tot (option (list expr)) (decreases js) =
  match js with
  | [] -> Some acc
  | j :: js' -> decode_expr_one sorts decls acc j >>= (fun e -> decode_exprs sorts decls (acc @ [e]) js')

let rec decode_indexed_exprs (sorts:list sort) (decls:list func_decl)
                            (acc:index_tree expr) (next:nat) (rev:list expr) (js:list json)
  : Tot (option (index_tree expr & list expr)) (decreases js) =
  match js with
  | [] -> Some (acc, rev)
  | j :: rest ->
    decode_expr_with sorts decls (index_find acc) j >>= (fun e ->
    decode_indexed_exprs sorts decls (index_put acc next e) (next + 1) (e :: rev) rest)

noeq
type proof_builders (a:Type) = {
  refl: expr -> a;
  sym: a -> a;
  trans: a -> a -> a;
  congr: func_decl -> list expr -> list expr -> list a -> a;
  rewrite: expr -> expr -> a;
  quant_intro: quantifier_kind -> list sort -> a -> a;
}

let decode_proof_with (#a:Type) (build:proof_builders a)
                      (sorts:list sort) (decls:list func_decl)
                      (expressions:int -> option expr) (previous:int -> option a) (j:json)
  : option a =
  json_obj j >>= (fun fields ->
  json_field fields "kind" >>= json_str >>= (fun kind ->
  if kind = "refl" then
    json_field fields "e" >>= json_int >>= expressions >>= (fun e -> Some (build.refl e))
  else if kind = "sym" then
    json_field fields "p" >>= json_int >>= previous >>= (fun p -> Some (build.sym p))
  else if kind = "trans" then
    json_field fields "p1" >>= json_int >>= previous >>= (fun p1 ->
    json_field fields "p2" >>= json_int >>= previous >>= (fun p2 ->
    Some (build.trans p1 p2)))
  else if kind = "congr" then
    json_field fields "decl" >>= json_int >>= nth_opt decls >>= (fun f ->
    json_field fields "args1" >>= json_arr >>= opt_map json_int >>= opt_map expressions >>= (fun args1 ->
    json_field fields "args2" >>= json_arr >>= opt_map json_int >>= opt_map expressions >>= (fun args2 ->
    json_field fields "prfs" >>= json_arr >>= opt_map json_int >>= opt_map previous >>= (fun prfs ->
    Some (build.congr f args1 args2 prfs)))))
  else if kind = "rewrite" then
    json_field fields "s" >>= json_int >>= expressions >>= (fun s ->
    json_field fields "t" >>= json_int >>= expressions >>= (fun t ->
    Some (build.rewrite s t)))
  else if kind = "quant_intro" then
    json_field fields "qk" >>= json_str >>= quantifier_kind_of_tag >>= (fun qk ->
    json_field fields "bound_sorts" >>= json_arr >>= opt_map json_int >>= opt_map (nth_opt sorts) >>= (fun bs ->
    json_field fields "p" >>= json_int >>= previous >>= (fun p ->
    Some (build.quant_intro qk bs p))))
  else None))

let tree_builders : proof_builders proof =
  { refl = Refl; sym = Sym; trans = Trans; congr = Congr;
    rewrite = Rewrite; quant_intro = QuantIntro }

let decode_proof_one (sorts:list sort) (decls:list func_decl) (exprs:list expr) (prev:list proof) (j:json)
  : option proof =
  decode_proof_with tree_builders sorts decls (nth_opt exprs) (nth_opt prev) j

let rec decode_proofs (sorts:list sort) (decls:list func_decl) (exprs:list expr) (acc:list proof) (js:list json)
  : Tot (option (list proof)) (decreases js) =
  match js with
  | [] -> Some acc
  | j :: js' -> decode_proof_one sorts decls exprs acc j >>= (fun p -> decode_proofs sorts decls exprs (acc @ [p]) js')

(* The refinement is erased: no recursive call to fact is extracted. *)
type cached_proof = {
  term: proof;
  result: r:option (expr & expr){r == fact term};
}

let cached_refl (e:expr) : cached_proof =
  { term = Refl e; result = Some (e, e) }

let cached_sym (p:cached_proof) : cached_proof =
  { term = Sym p.term;
    result = (match p.result with Some (a, b) -> Some (b, a) | None -> None) }

let cached_trans (p q:cached_proof) : cached_proof =
  { term = Trans p.term q.term;
    result = (match p.result, q.result with
              | Some (a, b), Some (c, d) -> if b = c then Some (a, d) else None
              | _, _ -> None) }

let rec cached_terms (ps:list cached_proof) : Tot (list proof) (decreases ps) =
  match ps with [] -> [] | p :: rest -> p.term :: cached_terms rest

let rec cached_results (ps:list cached_proof)
  : Tot (list (option (expr & expr))) (decreases ps) =
  match ps with [] -> [] | p :: rest -> p.result :: cached_results rest

let rec lemma_cached_results (ps:list cached_proof)
  : Lemma (cached_results ps == facts_of (cached_terms ps)) (decreases ps) =
  match ps with [] -> () | _ :: rest -> lemma_cached_results rest

let cached_congr (f:func_decl) (xs ys:list expr) (ps:list cached_proof) : cached_proof =
  lemma_cached_results ps;
  { term = Congr f xs ys (cached_terms ps);
    result = (if FStar.List.Tot.length xs = FStar.List.Tot.length ys &&
                 congr_matched xs ys (cached_results ps)
              then Some (App f xs, App f ys) else None) }

let cached_rewrite (s t:expr) : cached_proof =
  { term = Rewrite s t; result = Some (s, t) }

let cached_quant_intro (qk:quantifier_kind) (bs:list sort) (p:cached_proof) : cached_proof =
  { term = QuantIntro qk bs p.term;
    result = (match p.result with
              | Some (a, b) ->
                Some (Quantifier qk bs (quant_sort qk bs (get_sort a)) a,
                      Quantifier qk bs (quant_sort qk bs (get_sort b)) b)
              | None -> None) }

let cached_builders : proof_builders cached_proof =
  { refl = cached_refl; sym = cached_sym; trans = cached_trans; congr = cached_congr;
    rewrite = cached_rewrite; quant_intro = cached_quant_intro }

let rec decode_checked_proofs (sorts:list sort) (decls:list func_decl) (exprs:index_tree expr)
                              (acc:index_tree cached_proof) (next:nat) (js:list json)
  : Tot (option (index_tree cached_proof)) (decreases js) =
  match js with
  | [] -> Some acc
  | j :: rest ->
    decode_proof_with cached_builders sorts decls (index_find exprs) (index_find acc) j >>= (fun p ->
    decode_checked_proofs sorts decls exprs (index_put acc next p) (next + 1) rest)

(* ----------------------------------------------------------------- *)
(* 5. Top-level document decode                                       *)
(* ----------------------------------------------------------------- *)

(* `decode_doc j = Some (p, n)` means: `j` is a well-formed proof
   document (every array decodes, every index reference resolves
   within the already-decoded prefix of its target array, `root` is
   in range), `p` is the decoded root proof, and `n` is the document's
   declared `unmatched_count` annotation (carried through unchanged,
   for the harness's cross-check against
   `Z3PatternMatchedProofChecker.fst`'s `collect_unmatched`, exactly
   as the old `.fst`-generation path's `lemma_unmatched_count_cross_
   checked` did). *)
let decode_checked_doc (j:json) : option (cached_proof & int) =
  json_obj j >>= (fun fields ->
  json_field fields "sorts" >>= json_arr >>= decode_sorts [] >>= (fun sorts ->
  json_field fields "decls" >>= json_arr >>= decode_decls sorts [] >>= (fun decls ->
  json_field fields "exprs" >>= json_arr >>= decode_indexed_exprs sorts decls Empty 0 [] >>= (fun exprs ->
  json_field fields "proofs" >>= json_arr >>= decode_checked_proofs sorts decls (fst exprs) Empty 0 >>= (fun proofs ->
  json_field fields "root" >>= json_int >>= index_find proofs >>= (fun root ->
  json_field fields "unmatched_count" >>= json_int >>= (fun n ->
  Some (root, n))))))))

let decode_doc (j:json) : option (proof & int) =
  decode_checked_doc j >>= (fun (root, n) -> Some (root.term, n))

let parse_checked_proof_doc (s:string) : option (cached_proof & int) =
  match parse_json s with
  | Some j -> decode_checked_doc j
  | None -> None

let parse_proof_doc (s:string) : option (proof & int) =
  parse_checked_proof_doc s >>= (fun (root, n) -> Some (root.term, n))

(* ----------------------------------------------------------------- *)
(* 6. Pure, self-contained top-level entry points                     *)
(* ----------------------------------------------------------------- *)

(* `true` iff `s` parses to a well-formed proof document whose root
   proof is itself well-formed (`fact`-accepted, i.e. `check1_basic`
   would accept it, see `Z3ProofTheory.fst`). This does *not* by
   itself certify that the proof's `Rewrite` leaves are semantically
   sound -- see `Z3PulseProofCheckerJson.fst` for the Pulse-checked,
   end-to-end soundness-composed entry point that also discharges
   that via `Z3PatternMatchedProofChecker.fst`'s matcher library. *)
let check_proof_json_wf (s:string) : bool =
  match parse_checked_proof_doc s with
  | Some (p, _) -> Some? p.result
  | None -> false
