module Z3TypedRoot

(* G1 typed-root PROTOTYPE (branch fstar-typed-root-prototype-20261030, not production,
   not in the checker manifest, no executable checker or route change).

   A constructible typed carrier family and one standard ghost interpretation
   over the production sort-indexed value framework (Z3DatatypeValue trees,
   arguments and environments) and the production AST (Z3AstTheory sort/expr).

   Carriers (structural recursion on the sort, independent of the schema):
     Bool  -> bool
     Int   -> int
     Real  -> FStar.Real.real (every real)
     (Array d1 .. dn r) -> func_space (d1 * .. * dn) r: restricted ghost
                           functions over the index carriers (all functions,
                           no finite-store or constant-array restriction)
     any other base sort -> u.sort_carrier s, an arbitrary nonempty Type0 chosen by
                           the model (uninterpreted sorts; BV/FF/Seq/FP/String/... are
                           NOT interpreted in this prototype)
   Datatype sorts never use their carrier: their values are the existing
   checked constructor trees (V.has_sort rejects a Scalar at a datatype sort).
   Arrays whose sort mentions a datatype (V.contains_datatype) are OUTSIDE the
   supported domain: their carrier is a nonempty placeholder and every operator
   on them (select/store/lambda/...) is a free model choice with no array law.

   Interpreted operators (canonical metadata only, see `classify`): true, false,
   not, =>, n-ary and/or/xor, = at every sort, ite at every sort, Int and Real
   numerals (op_num_rational), + * - over Int or Real, Real / with a nonzero
   divisor, to_real, <= < >= > over Int or Real, select and store at every
   supported array sort (any arity, nested), lambda at every supported array
   sort, forall/exists over every sort. Everything else is a free choice in
   `symbols` (uninterpreted symbols, Int div/mod/abs, distinct, const-array,
   array-ext, BV/FF/Seq/FP operators, real division by zero, ill-matched
   datatype selectors, operators and lambdas at unsupported sorts).

   Contract: `root_model` (R1 quantifiers, R2 operators, R3 lambdas, R4
   constructors). L1 `lemma_standard_root`: `standard u sch uf` satisfies it for
   EVERY u and uf over every `supported` schema. *)

open Z3AstTheory
open Z3ValueTheory
open FStar.List.Tot
open FStar.Real
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module A = Z3LinearArithmeticAst
module R = Z3ResolutionProofTheory
module B = Z3BoundedBoolEquiv
module D = Z3Definitions
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module FE = FStar.FunctionalExtensionality
module ID = FStar.IndefiniteDescription

(* ---------------------------------------------------------------------- *)
(* Carriers                                                                 *)
(* ---------------------------------------------------------------------- *)

(* The only model-owned carriers: arbitrary nonempty families. *)
noeq type uninterpreted = {
  sort_carrier: sort -> Type0;
  inhabitant: s:sort -> sort_carrier s;
}

(* Unrestricted total ghost functions, restricted to their domain so that
   pointwise equality implies equality (FE.extensionality_g). Named, so
   that every use refers to one closure. *)
let func_space (a b:Type0) : Type0 = FE.restricted_g_t a (fun _ -> b)

let lambda_value (#a #b:Type0) (f:a -> GTot b) : func_space a b = FE.on_dom_g a f

let rec carrier (u:uninterpreted) (s:sort) : Tot Type0 (decreases s) =
  match s with
  | BaseSort "Bool" -> bool
  | BaseSort "Int" -> int
  | BaseSort "Real" -> real
  | BaseSort _ -> u.sort_carrier s
  | ArraySort ds r -> func_space (indices u ds) (carrier u r)

and indices (u:uninterpreted) (ds:list sort) : Tot Type0 (decreases ds) =
  match ds with
  | [] -> unit
  | d :: rest -> carrier u d & indices u rest

let real_s : sort = A.real_s
let int_s : sort = A.int_s

let lemma_carriers (u:uninterpreted)
  : Lemma (carrier u bool_sort == bool /\ carrier u int_s == int /\ carrier u real_s == real /\
           carrier u (ArraySort [int_s] real_s) == FE.restricted_g_t (int & unit) (fun _ -> real)) =
  assert_norm (carrier u bool_sort == bool);
  assert_norm (carrier u int_s == int);
  assert_norm (carrier u real_s == real);
  assert_norm (carrier u (ArraySort [int_s] real_s) == FE.restricted_g_t (int & unit) (fun _ -> real))

let lemma_array_carrier (u:uninterpreted) (ds:list sort) (r:sort)
  : Lemma (carrier u (ArraySort ds r) == func_space (indices u ds) (carrier u r))
          [SMTPat (carrier u (ArraySort ds r))] =
  assert_norm (carrier u (ArraySort ds r) == func_space (indices u ds) (carrier u r))

let lemma_indices_cons (u:uninterpreted) (d:sort) (rest:list sort)
  : Lemma (indices u (d :: rest) == (carrier u d & indices u rest))
          [SMTPat (indices u (d :: rest))] =
  assert_norm (indices u (d :: rest) == (carrier u d & indices u rest))

(* Every carrier is inhabited (a Tot witness, no choice). *)
let rec default_value (u:uninterpreted) (s:sort) : Tot (carrier u s) (decreases s) =
  match s with
  | BaseSort "Bool" -> false
  | BaseSort "Int" -> 0
  | BaseSort "Real" -> 0.0R
  | BaseSort _ -> u.inhabitant s
  | ArraySort ds r ->
    lemma_array_carrier u ds r;
    coerce_eq #(func_space (indices u ds) (carrier u r)) #(carrier u s) ()
      (lambda_value #(indices u ds) #(carrier u r) (fun _ -> default_value u r))

(* The only classical choice used by the standard model. *)
let decide (p:prop) : GTot (b:bool{b <==> p}) = ID.strong_excluded_middle p

(* ---------------------------------------------------------------------- *)
(* Supported domain and conversions between trees and carriers             *)
(* ---------------------------------------------------------------------- *)

(* A sort is in the supported (standard) domain iff it mentions no datatype
   sort of the schema. Executable, structural, schema-dependent. *)
let free (sigma:V.signature) (s:sort) : bool = not (V.contains_datatype sigma s)

let rec lemma_registered (sigma:V.signature) (f:func_decl)
  : Lemma (requires L.mem f sigma) (ensures V.datatype_sort sigma f.range) (decreases sigma) =
  match sigma with [] -> () | g :: rest -> if f <> g then lemma_registered rest f

let scalar (#u:uninterpreted) (#sigma:V.signature) (t:sort{not (V.datatype_sort sigma t)})
           (v:V.value (carrier u) sigma t) : carrier u t =
  match v with
  | V.Scalar t' x -> coerce_eq #(carrier u t') #(carrier u t) () x
  | V.Constructor f _ -> lemma_registered sigma f; FStar.Pervasives.false_elim ()

let make (#u:uninterpreted) (#sigma:V.signature) (t:sort{not (V.datatype_sort sigma t)})
         (x:carrier u t) : V.value (carrier u) sigma t =
  V.Scalar t x

let lemma_scalar_make (#u:uninterpreted) (#sigma:V.signature) (t:sort{not (V.datatype_sort sigma t)})
                      (x:carrier u t)
  : Lemma (scalar #u #sigma t (make t x) == x) [SMTPat (scalar #u #sigma t (make t x))] = ()

let lemma_make_scalar (#u:uninterpreted) (#sigma:V.signature) (t:sort{not (V.datatype_sort sigma t)})
                      (v:V.value (carrier u) sigma t)
  : Lemma (make t (scalar t v) == v) [SMTPat (scalar #u #sigma t v)] =
  match v with
  | V.Scalar _ _ -> ()
  | V.Constructor f _ -> lemma_registered sigma f

let rec to_indices (#u:uninterpreted) (#sigma:V.signature)
                   (ds:list sort{not (V.contains_datatype_args sigma ds)})
                   (xs:V.arguments (carrier u) sigma ds)
  : Tot (indices u ds) (decreases ds) =
  match ds, xs with
  | [], [] -> ()
  | d :: rest, x :: tail ->
    coerce_eq #(carrier u d & indices u rest) #(indices u ds) ()
      (scalar #u #sigma d x, to_indices #u #sigma rest tail)
  | _, _ -> FStar.Pervasives.false_elim ()

let rec from_indices (#u:uninterpreted) (#sigma:V.signature)
                     (ds:list sort{not (V.contains_datatype_args sigma ds)})
                     (ix:indices u ds)
  : Tot (V.arguments (carrier u) sigma ds) (decreases ds) =
  match ds with
  | [] -> []
  | d :: rest ->
    let p = coerce_eq #(indices u ds) #(carrier u d & indices u rest) () ix in
    make #u #sigma d (fst p) :: from_indices #u #sigma rest (snd p)

let rec lemma_to_from (#u:uninterpreted) (#sigma:V.signature)
                      (ds:list sort{not (V.contains_datatype_args sigma ds)})
                      (ix:indices u ds)
  : Lemma (ensures to_indices #u #sigma ds (from_indices #u #sigma ds ix) == ix) (decreases ds) =
  match ds with
  | [] -> ()
  | d :: rest ->
    let p = coerce_eq #(indices u ds) #(carrier u d & indices u rest) () ix in
    lemma_to_from #u #sigma rest (snd p)

let rec lemma_from_to (#u:uninterpreted) (#sigma:V.signature)
                      (ds:list sort{not (V.contains_datatype_args sigma ds)})
                      (xs:V.arguments (carrier u) sigma ds)
  : Lemma (ensures from_indices #u #sigma ds (to_indices #u #sigma ds xs) == xs) (decreases ds) =
  match ds, xs with
  | [], [] -> ()
  | d :: rest, x :: tail ->
    lemma_from_to #u #sigma rest tail;
    lemma_make_scalar #u #sigma d x;
    assert (to_indices #u #sigma ds xs == (scalar #u #sigma d x, to_indices #u #sigma rest tail))
  | _, _ -> ()

let rec append_arguments (#base:sort -> Type0) (sigma:V.signature) (xs ys:list sort)
                         (vs:V.arguments base sigma xs) (ws:V.arguments base sigma ys)
  : Tot (V.arguments base sigma (xs @ ys)) (decreases xs) =
  match xs, vs with
  | [], [] -> ws
  | _ :: rest, v :: tail -> v :: append_arguments sigma rest ys tail ws
  | _, _ -> FStar.Pervasives.false_elim ()

(* Typed reversal: lambda bodies take their arguments innermost-first
   (L.rev bound), array indices are written outermost-first. *)
let rec reverse_arguments (#base:sort -> Type0) (sigma:V.signature) (xs:list sort)
                          (vs:V.arguments base sigma xs)
  : Tot (V.arguments base sigma (L.rev xs)) (decreases xs) =
  match xs, vs with
  | [], [] -> []
  | x :: rest, v :: tail ->
    LP.rev_rev' (x :: rest); LP.rev_rev' rest;
    append_arguments sigma (L.rev rest) [x] (reverse_arguments sigma rest tail) [v]
  | _, _ -> FStar.Pervasives.false_elim ()

(* ---------------------------------------------------------------------- *)
(* Free model choices                                                       *)
(* ---------------------------------------------------------------------- *)

type tvalue (u:uninterpreted) (sch:S.checked_schema) (t:sort) = V.value (carrier u) (S.signature sch) t
type targuments (u:uninterpreted) (sch:S.checked_schema) (ts:list sort) =
  V.arguments (carrier u) (S.signature sch) ts

(* Every remaining choice of a model, with NO constraint: uninterpreted
   symbols, every operator outside the interpreted set below (including
   integer div/mod, distinct, BV/FF/Seq/FP operators), real division by
   zero, ill-matched datatype selectors, and every operator or lambda at a
   sort mentioning a datatype. *)
noeq type symbols (u:uninterpreted) (sch:S.checked_schema) = {
  apply: f:func_decl -> targuments u sch f.domain -> GTot (tvalue u sch f.range);
  lambda: bound:list sort -> t:sort -> (targuments u sch (L.rev bound) -> GTot (tvalue u sch t)) ->
          GTot (tvalue u sch (ArraySort bound t));
}

(* ---------------------------------------------------------------------- *)
(* Interpreted operators: classification from canonical metadata only      *)
(* ---------------------------------------------------------------------- *)

let rec boolean_sorts (ss:list sort) : Tot bool (decreases ss) =
  match ss with [] -> true | s :: rest -> s = bool_sort && boolean_sorts rest

let rec same_sorts (t:sort) (ss:list sort) : Tot bool (decreases ss) =
  match ss with [] -> true | s :: rest -> s = t && same_sorts t rest

let ite_decl (s:sort) : func_decl = {
  decl_name = "if"; domain = [bool_sort; s; s]; range = s; interp = Some op_ite; int_params = [];
}

let select_decl (ds:list sort) (r:sort) : func_decl = {
  decl_name = "select"; domain = ArraySort ds r :: ds; range = r;
  interp = Some op_select; int_params = [];
}

let store_decl (ds:list sort) (r:sort) : func_decl = {
  decl_name = "store"; domain = ArraySort ds r :: (ds @ [r]); range = ArraySort ds r;
  interp = Some op_store; int_params = [];
}

type theory_op =
  | Constant : bool -> theory_op
  | Negation
  | Implication
  | Nary : B.nary_op -> theory_op
  | Equality : sort -> theory_op
  | Choice : sort -> theory_op
  | Numeral : sort -> int -> pos -> theory_op
  | Arith : sort -> A.operation -> theory_op
  | Divide
  | ToReal
  | Compare : sort -> A.relation -> theory_op
  | Select : list sort -> sort -> theory_op
  | Store : list sort -> sort -> theory_op
  | Other

let op_typed (sigma:V.signature) (f:func_decl) (op:theory_op) : bool =
  match op with
  | Constant _ -> f.domain = [] && f.range = bool_sort
  | Negation -> f.domain = [bool_sort] && f.range = bool_sort
  | Implication -> f.domain = [bool_sort; bool_sort] && f.range = bool_sort
  | Nary _ -> boolean_sorts f.domain && f.range = bool_sort
  | Equality s -> f.domain = [s; s] && f.range = bool_sort
  | Choice s -> f.domain = [bool_sort; s; s] && f.range = s
  | Numeral s _ d ->
    f.domain = [] && f.range = s && (s = int_s || s = real_s) && not (V.datatype_sort sigma s) &&
    (s = real_s || d = 1)
  | Arith s o ->
    f.range = s && same_sorts s f.domain && (s = int_s || s = real_s) &&
    not (V.datatype_sort sigma s) && (o = A.Add || o = A.Mul || o = A.Sub)
  | Divide -> f.domain = [real_s; real_s] && f.range = real_s && not (V.datatype_sort sigma real_s)
  | ToReal -> f.domain = [int_s] && f.range = real_s && not (V.datatype_sort sigma real_s) &&
              not (V.datatype_sort sigma int_s)
  | Compare s r ->
    f.domain = [s; s] && f.range = bool_sort && (s = int_s || s = real_s) &&
    not (V.datatype_sort sigma s) && r <> A.Eq
  | Select ds r -> f = select_decl ds r && free sigma (ArraySort ds r)
  | Store ds r -> f = store_decl ds r && free sigma (ArraySort ds r)
  | Other -> true

(* Same tests as Z3SortedSemantics.classify (G1-local copy, because the
   Sorted modules downstream of the GTot change are not migrated in G1). *)
let connective (f:func_decl) : theory_op =
  if f = { decl_name = "true"; domain = []; range = bool_sort;
           interp = Some op_true; int_params = [] } then Constant true
  else if f = { decl_name = "false"; domain = []; range = bool_sort;
                interp = Some op_false; int_params = [] } then Constant false
  else if f = { decl_name = "not"; domain = [bool_sort]; range = bool_sort;
                interp = Some op_not; int_params = [] } then Negation
  else if (f.decl_name = "=>" || f.decl_name = "implies") &&
          f.domain = [bool_sort; bool_sort] && f.range = bool_sort &&
          f.interp = Some op_implies && f.int_params = [] then Implication
  else if f.range = bool_sort && boolean_sorts f.domain && f.int_params = [] &&
          (f.decl_name = "and" && f.interp = Some op_and ||
           f.decl_name = "or" && f.interp = Some op_or ||
           f.decl_name = "xor" && f.interp = Some op_xor) then
    Nary (if f.interp = Some op_and then B.And
          else if f.interp = Some op_or then B.Or else B.Xor)
  else match f.domain with
  | [s; _] -> if f = R.eq_decl s then Equality s else Other
  | [_; s; _] -> if f = ite_decl s then Choice s else Other
  | _ -> Other

let numeric (sigma:V.signature) (f:func_decl) : theory_op =
  let s = f.range in
  if (s = int_s || s = real_s) && not (V.datatype_sort sigma s) && f.domain = [] then
    (match A.numeral (App f []) with
     | Some (n, d) -> if s = real_s || d = 1 then Numeral s n d else Other
     | None -> Other)
  else if (s = int_s || s = real_s) && not (V.datatype_sort sigma s) && same_sorts s f.domain then
    (match A.operation_of f (S.dummy_fields f.domain) with
     | Some A.Add -> Arith s A.Add
     | Some A.Mul -> Arith s A.Mul
     | Some A.Sub -> Arith s A.Sub
     | Some A.Div -> if s = real_s && f.domain = [real_s; real_s] then Divide else Other
     | _ -> Other)
  else if s = real_s && f.domain = [int_s] && not (V.datatype_sort sigma real_s) &&
          not (V.datatype_sort sigma int_s) then
    (match A.operation_of f (S.dummy_fields f.domain) with Some A.ToReal -> ToReal | _ -> Other)
  else match f.domain with
  | [a; b] ->
    if a = b && (a = int_s || a = real_s) && f.range = bool_sort && not (V.datatype_sort sigma a) then
      (match A.comparison (App f [Var 0 a; Var 0 a]) with
       | Some (r, _, _) -> if r <> A.Eq then Compare a r else Other
       | None -> Other)
    else Other
  | _ -> Other

let array_op (sigma:V.signature) (f:func_decl) : theory_op =
  match f.domain with
  | ArraySort ds r :: _ ->
    if not (free sigma (ArraySort ds r)) then Other
    else if f = select_decl ds r then Select ds r
    else if f = store_decl ds r then Store ds r
    else Other
  | _ -> Other

let classify (sigma:V.signature) (f:func_decl) : op:theory_op{op_typed sigma f op} =
  match connective f with
  | Other ->
    (match numeric sigma f with
     | Other -> array_op sigma f
     | op -> op)
  | op -> op

(* ---------------------------------------------------------------------- *)
(* The standard theory layer                                               *)
(* ---------------------------------------------------------------------- *)

let boolean (#u:uninterpreted) (sch:S.checked_schema) (b:bool) : tvalue u sch bool_sort =
  make #u #(S.signature sch) bool_sort b

let truth (#u:uninterpreted) (sch:S.checked_schema) (v:tvalue u sch bool_sort) : bool =
  scalar #u #(S.signature sch) bool_sort v

let rec truths (#u:uninterpreted) (sch:S.checked_schema)
               (ss:list sort{boolean_sorts ss}) (xs:targuments u sch ss)
  : Tot (list bool) (decreases ss) =
  match ss, xs with
  | [], [] -> []
  | _ :: rest, x :: tail -> truth sch x :: truths sch rest tail
  | _, _ -> FStar.Pervasives.false_elim ()

let rec combine (op:B.nary_op) (xs:list bool) : Tot bool (decreases xs) =
  match xs with [] -> B.neutral op | x :: rest -> B.combine op x (combine op rest)

let rec ints (#u:uninterpreted) (sch:S.checked_schema)
             (ss:list sort{same_sorts int_s ss}) (xs:targuments u sch ss)
  : Tot (list int) (decreases ss) =
  match ss, xs with
  | [], [] -> []
  | _ :: rest, x :: tail -> scalar #u #(S.signature sch) int_s x :: ints sch rest tail
  | _, _ -> FStar.Pervasives.false_elim ()

let rec reals (#u:uninterpreted) (sch:S.checked_schema{not (V.datatype_sort (S.signature sch) real_s)})
              (ss:list sort{same_sorts real_s ss}) (xs:targuments u sch ss)
  : Tot (list real) (decreases ss) =
  match ss, xs with
  | [], [] -> []
  | _ :: rest, x :: tail -> scalar #u #(S.signature sch) real_s x :: reals sch rest tail
  | _, _ -> FStar.Pervasives.false_elim ()

let rec isum (xs:list int) : Tot int (decreases xs) =
  match xs with [] -> 0 | x :: rest -> x + isum rest
let rec iproduct (xs:list int) : Tot int (decreases xs) =
  match xs with [] -> 1 | x :: rest -> x * iproduct rest
let isubtract (xs:list int) : int =
  match xs with [] -> 0 | [x] -> -x | x :: rest -> x - isum rest

let rec rsum (xs:list real) : Tot real (decreases xs) =
  match xs with [] -> 0.0R | x :: rest -> x +. rsum rest
let rec rproduct (xs:list real) : Tot real (decreases xs) =
  match xs with [] -> 1.0R | x :: rest -> x *. rproduct rest
let rsubtract (xs:list real) : real =
  match xs with [] -> 0.0R | [x] -> 0.0R -. x | x :: rest -> x -. rsum rest

let icalculate (o:A.operation) (xs:list int) : int =
  match o with A.Add -> isum xs | A.Mul -> iproduct xs | _ -> isubtract xs
let rcalculate (o:A.operation) (xs:list real) : real =
  match o with A.Add -> rsum xs | A.Mul -> rproduct xs | _ -> rsubtract xs

let icompare (r:A.relation) (x y:int) : bool =
  match r with A.Le -> x <= y | A.Lt -> x < y | A.Ge -> y <= x | A.Gt -> y < x | A.Eq -> x = y

let rcompare (r:A.relation) (x y:real) : GTot bool =
  match r with
  | A.Le -> decide (x <=. y) | A.Lt -> decide (x <. y)
  | A.Ge -> decide (y <=. x) | A.Gt -> decide (y <. x) | A.Eq -> decide (x == y)

let rational (n:int) (d:pos) : real = of_int n /. of_int d

let rec split_store (#u:uninterpreted) (#sigma:V.signature)
                    (ds:list sort{not (V.contains_datatype_args sigma ds)})
                    (r:sort{not (V.datatype_sort sigma r)})
                    (xs:V.arguments (carrier u) sigma (ds @ [r]))
  : Tot (indices u ds & carrier u r) (decreases ds) =
  match ds, xs with
  | [], [v] -> ((), scalar #u #sigma r v)
  | d :: rest, x :: tail ->
    let p = split_store #u #sigma rest r tail in
    (coerce_eq #(carrier u d & indices u rest) #(indices u ds) () (scalar #u #sigma d x, fst p), snd p)
  | _, _ -> FStar.Pervasives.false_elim ()

let read (#a #b:Type0) (fn:func_space a b) (i:a) : GTot b = fn i

let write (#a #b:Type0) (fn:func_space a b) (i:a) (v:b) : func_space a b =
  lambda_value #a #b (fun j -> if decide (j == i) then v else fn j)

(* The standard meaning of every interpreted operator, independent of the
   free choices. None exactly when SMT-LIB leaves the value unconstrained
   (an operator outside the interpreted set, or a real division by zero). *)
let interpreted (u:uninterpreted) (sch:S.checked_schema)
                (f:func_decl) (xs:targuments u sch f.domain)
  : GTot (option (tvalue u sch f.range)) =
  let sigma = S.signature sch in
  match classify sigma f with
  | Constant b -> Some (boolean sch b)
  | Negation ->
    (match xs with [x] -> Some (boolean sch (not (truth sch x))) | _ -> FStar.Pervasives.false_elim ())
  | Implication ->
    (match xs with
     | [x; y] -> Some (boolean sch (not (truth sch x) || truth sch y))
     | _ -> FStar.Pervasives.false_elim ())
  | Nary op -> Some (boolean sch (combine op (truths sch f.domain xs)))
  | Equality _ ->
    (match xs with [x; y] -> Some (boolean sch (decide (x == y))) | _ -> FStar.Pervasives.false_elim ())
  | Choice _ ->
    (match xs with [c; x; y] -> Some (if truth sch c then x else y) | _ -> FStar.Pervasives.false_elim ())
  | Numeral s n d ->
    if s = int_s then Some (make #u #sigma int_s n) else Some (make #u #sigma real_s (rational n d))
  | Arith s o ->
    if s = int_s then Some (make #u #sigma int_s (icalculate o (ints sch f.domain xs)))
    else Some (make #u #sigma real_s (rcalculate o (reals sch f.domain xs)))
  | Divide ->
    (match xs with
     | [x; y] ->
       let a = scalar #u #sigma real_s x in
       let b = scalar #u #sigma real_s y in
       if decide (b == 0.0R) then None   (* division by zero: a free model choice *)
       else Some (make #u #sigma real_s (a /. b))
     | _ -> FStar.Pervasives.false_elim ())
  | ToReal ->
    (match xs with
     | [x] -> Some (make #u #sigma real_s (of_int (scalar #u #sigma int_s x)))
     | _ -> FStar.Pervasives.false_elim ())
  | Compare s r ->
    (match xs with
     | [x; y] ->
       if s = int_s then Some (boolean sch (icompare r (scalar #u #sigma int_s x) (scalar #u #sigma int_s y)))
       else Some (boolean sch (rcompare r (scalar #u #sigma real_s x) (scalar #u #sigma real_s y)))
     | _ -> FStar.Pervasives.false_elim ())
  | Select ds r ->
    (match xs with
     | a :: ix ->
       Some (make #u #sigma r (read #(indices u ds) #(carrier u r)
                                (scalar #u #sigma (ArraySort ds r) a) (to_indices #u #sigma ds ix)))
     | _ -> FStar.Pervasives.false_elim ())
  | Store ds r ->
    (match xs with
     | a :: rest ->
       let p = split_store #u #sigma ds r rest in
       Some (make #u #sigma (ArraySort ds r)
         (write #(indices u ds) #(carrier u r) (scalar #u #sigma (ArraySort ds r) a) (fst p) (snd p)))
     | _ -> FStar.Pervasives.false_elim ())
  | Other -> None

let theory_application (u:uninterpreted) (sch:S.checked_schema) (uf:symbols u sch)
                       (f:func_decl) (xs:targuments u sch f.domain)
  : GTot (tvalue u sch f.range) =
  match interpreted u sch f xs with
  | Some v -> v
  | None -> uf.apply f xs

(* Truth of a tree: the Boolean scalar true. *)
let holds (#u:uninterpreted) (v:V.tree (carrier u)) : prop =
  v == V.Scalar bool_sort (true <: carrier u bool_sort)

(* The graph of a lambda at a supported sort: array indices are given
   outermost-first (the order of the binder list), the body expects them
   innermost-first (de Bruijn, L.rev bound). *)
let graph (u:uninterpreted) (sch:S.checked_schema) (bound:list sort) (t:sort{free (S.signature sch) (ArraySort bound t)})
          (body:targuments u sch (L.rev bound) -> GTot (tvalue u sch t))
  : func_space (indices u bound) (carrier u t) =
  let sigma = S.signature sch in
  lambda_value #(indices u bound) #(carrier u t) (fun ix ->
    scalar #u #sigma t (body (reverse_arguments sigma bound (from_indices #u #sigma bound ix))))

let quantification (u:uninterpreted) (sch:S.checked_schema) (uf:symbols u sch)
                   (k:quantifier_kind) (bound:list sort) (t:sort)
                   (body:targuments u sch (L.rev bound) -> GTot (tvalue u sch t))
  : GTot (tvalue u sch (quant_sort k bound t)) =
  let sigma = S.signature sch in
  match k with
  | Forall_k -> boolean sch (decide (forall (vs:targuments u sch (L.rev bound)). holds (body vs)))
  | Exists_k -> boolean sch (decide (exists (vs:targuments u sch (L.rev bound)). holds (body vs)))
  | Lambda_k ->
    if free sigma (ArraySort bound t) then make #u #sigma (ArraySort bound t) (graph u sch bound t body)
    else uf.lambda bound t body

let theory (u:uninterpreted) (sch:S.checked_schema) (uf:symbols u sch)
  : V.interpretation (carrier u) (S.signature sch) = {
  application = theory_application u sch uf;
  quantification = quantification u sch uf;
}

let booleans (u:uninterpreted) : S.boolean_carrier (carrier u) = {
  encode_bool = (fun (b:bool) -> (b <: carrier u bool_sort));
  decode_bool = (fun (b:carrier u bool_sort) -> (b <: bool));
  boolean_isomorphism = ();
}

(* THE standard model: the production datatype layer (constructors,
   recognizers, accessors; ill-matched selectors go to the free choice)
   over the standard theory layer. One interpretation for every u and uf. *)
let standard (u:uninterpreted) (sch:S.checked_schema) (uf:symbols u sch)
  : V.interpretation (carrier u) (S.signature sch) =
  S.interpretation sch (booleans u) (theory u sch uf)

(* ---------------------------------------------------------------------- *)
(* Supported schemas                                                        *)
(* ---------------------------------------------------------------------- *)

let rec base_owned (sigma:V.signature) : Tot bool (decreases sigma) =
  match sigma with [] -> true | f :: rest -> BaseSort? f.range && base_owned rest

(* The claimed support domain of the root theorem, as an executable check.
   S.valid already rejects a datatype at Bool or Int, but NOT a datatype
   registered under the name "Real", nor a constructor whose range is an
   array sort. A future root validator must establish `supported` before
   any theory or array acceptance relies on these laws; it is not implied
   by S.valid. *)
let supported (sch:S.schema) : bool =
  S.valid sch && not (V.datatype_sort (S.signature sch) real_s) && base_owned (S.signature sch)

type supported_schema = sch:S.checked_schema{supported sch}

(* ---------------------------------------------------------------------- *)
(* The typed root contract                                                  *)
(* ---------------------------------------------------------------------- *)

let datatype_kind (f:func_decl) : bool =
  f.interp = Some Z3DatatypeLemma.op_constructor || f.interp = Some Z3DatatypeLemma.op_recognizer ||
  f.interp = Some Z3DatatypeLemma.op_accessor

type interp (u:uninterpreted) (sch:S.checked_schema) = V.interpretation (carrier u) (S.signature sch)

(* Named ghost body types, so that every statement quantifies over one type. *)
type body_of (u:uninterpreted) (sch:S.checked_schema) (bound:list sort) (t:sort) =
  targuments u sch (L.rev bound) -> GTot (tvalue u sch t)

(* R1: classical quantifiers over the full typed carriers (every Int, every
   real, every ghost function, every checked constructor tree, every element
   of each uninterpreted carrier), with heterogeneous typed binder lists. *)
let forall_case (u:uninterpreted) (sch:S.checked_schema) (i:interp u sch)
                (bound:list sort) (body:body_of u sch bound bool_sort) : prop =
  truth sch (i.quantification Forall_k bound bool_sort body) <==>
  (forall (vs:targuments u sch (L.rev bound)). truth sch (body vs))

let exists_case (u:uninterpreted) (sch:S.checked_schema) (i:interp u sch)
                (bound:list sort) (body:body_of u sch bound bool_sort) : prop =
  truth sch (i.quantification Exists_k bound bool_sort body) <==>
  (exists (vs:targuments u sch (L.rev bound)). truth sch (body vs))

let quantifier_laws (u:uninterpreted) (sch:S.checked_schema) (i:interp u sch) : prop =
  (forall (bound:list sort) (body:body_of u sch bound bool_sort). forall_case u sch i bound body) /\
  (forall (bound:list sort) (body:body_of u sch bound bool_sort). exists_case u sch i bound body)

(* R2: every interpreted (non-datatype) operator has its standard meaning
   wherever SMT-LIB determines it. *)
let operator_law (u:uninterpreted) (sch:S.checked_schema) (i:interp u sch) : prop =
  forall (f:func_decl) (xs:targuments u sch f.domain).
    (not (datatype_kind f) /\ Some? (interpreted u sch f xs)) ==>
    i.application f xs == Some?.v (interpreted u sch f xs)

(* R3: a lambda at a supported sort denotes its graph. *)
let lambda_law (u:uninterpreted) (sch:S.checked_schema) (i:interp u sch) : prop =
  forall (bound:list sort) (t:sort{free (S.signature sch) (ArraySort bound t)})
         (body:body_of u sch bound t).
    i.quantification Lambda_k bound t body ==
    make #u #(S.signature sch) (ArraySort bound t) (graph u sch bound t body)

(* R4: constructors build the checked constructor trees. *)
let constructor_law (u:uninterpreted) (sch:S.checked_schema) (i:interp u sch) : prop =
  forall (f:func_decl{L.mem f (S.signature sch)}) (xs:targuments u sch f.domain).
    i.application f xs == V.construct (S.signature sch) f xs

let root_model (u:uninterpreted) (sch:S.checked_schema) (i:interp u sch) : prop =
  quantifier_laws u sch i /\ operator_law u sch i /\ lambda_law u sch i /\ constructor_law u sch i

(* ---------------------------------------------------------------------- *)
(* L1: the standard model satisfies the root contract, for EVERY choice of  *)
(* uninterpreted carriers u and free symbols uf                             *)
(* ---------------------------------------------------------------------- *)

let lemma_holds (#u:uninterpreted) (sch:S.checked_schema) (v:tvalue u sch bool_sort)
  : Lemma (holds v <==> truth sch v == true) =
  match v with
  | V.Scalar _ _ -> ()
  | V.Constructor f _ -> lemma_registered (S.signature sch) f

let lemma_truth_boolean (#u:uninterpreted) (sch:S.checked_schema) (b:bool)
  : Lemma (truth #u sch (boolean sch b) == b) [SMTPat (truth #u sch (boolean sch b))] = ()

let rec lemma_no_recognizer (f:func_decl) (cs:list S.constructor_case)
  : Lemma (requires not (datatype_kind f)) (ensures None? (S.find_recognizer f cs)) (decreases cs) =
  match cs with [] -> () | _ :: rest -> lemma_no_recognizer f rest

let rec lemma_no_accessor (f:func_decl) (cs:list S.constructor_case)
  : Lemma (requires not (datatype_kind f)) (ensures None? (S.find_accessor f cs)) (decreases cs) =
  match cs with [] -> () | _ :: rest -> lemma_no_accessor f rest

let lemma_not_constructor (sch:S.checked_schema) (f:func_decl)
  : Lemma (requires not (datatype_kind f)) (ensures not (L.mem f (S.signature sch))) =
  if L.mem f (S.signature sch) then begin
    S.lemma_case_of sch.cases f;
    let c = Some?.v (S.case_of sch.cases f) in
    S.lemma_case_member (S.signature sch) sch.sorts sch.cases c
  end

let lemma_standard_application (u:uninterpreted) (sch:S.checked_schema) (uf:symbols u sch)
                               (f:func_decl) (xs:targuments u sch f.domain)
  : Lemma (requires not (datatype_kind f))
          (ensures (standard u sch uf).application f xs == theory_application u sch uf f xs) =
  lemma_not_constructor sch f;
  lemma_no_recognizer f sch.cases;
  lemma_no_accessor f sch.cases

let lemma_forall_case (u:uninterpreted) (sch:S.checked_schema) (uf:symbols u sch)
                      (bound:list sort) (body:body_of u sch bound bool_sort)
  : Lemma (forall_case u sch (standard u sch uf) bound body) =
  let aux (vs:targuments u sch (L.rev bound)) : Lemma (holds (body vs) <==> truth sch (body vs) == true) =
    lemma_holds sch (body vs) in
  FStar.Classical.forall_intro aux

let lemma_exists_case (u:uninterpreted) (sch:S.checked_schema) (uf:symbols u sch)
                      (bound:list sort) (body:body_of u sch bound bool_sort)
  : Lemma (exists_case u sch (standard u sch uf) bound body) =
  let aux (vs:targuments u sch (L.rev bound)) : Lemma (holds (body vs) <==> truth sch (body vs) == true) =
    lemma_holds sch (body vs) in
  FStar.Classical.forall_intro aux

let lemma_quantifier_laws (u:uninterpreted) (sch:S.checked_schema) (uf:symbols u sch)
  : Lemma (quantifier_laws u sch (standard u sch uf)) =
  FStar.Classical.forall_intro_2 (lemma_forall_case u sch uf);
  FStar.Classical.forall_intro_2 (lemma_exists_case u sch uf)

let lemma_operator_law (u:uninterpreted) (sch:S.checked_schema) (uf:symbols u sch)
  : Lemma (operator_law u sch (standard u sch uf)) =
  let aux (f:func_decl) (xs:targuments u sch f.domain)
    : Lemma ((not (datatype_kind f) /\ Some? (interpreted u sch f xs)) ==>
             (standard u sch uf).application f xs == Some?.v (interpreted u sch f xs)) =
    if not (datatype_kind f) then lemma_standard_application u sch uf f xs in
  FStar.Classical.forall_intro_2 aux

let lemma_lambda_law (u:uninterpreted) (sch:S.checked_schema) (uf:symbols u sch)
  : Lemma (lambda_law u sch (standard u sch uf)) = ()

let lemma_constructor_law (u:uninterpreted) (sch:S.checked_schema) (uf:symbols u sch)
  : Lemma (constructor_law u sch (standard u sch uf)) = ()

(* L1. No hypothesis on u or uf: one joint positive model for every free choice. *)
let lemma_standard_root (u:uninterpreted) (sch:supported_schema) (uf:symbols u sch)
  : Lemma (root_model u sch (standard u sch uf)) =
  lemma_quantifier_laws u sch uf;
  lemma_operator_law u sch uf;
  lemma_lambda_law u sch uf;
  lemma_constructor_law u sch uf

(* Non-vacuity: the class of root models is inhabited for every supported
   schema and every choice of uninterpreted carriers. *)
let lemma_root_inhabited (u:uninterpreted) (sch:supported_schema)
  : Lemma (exists (i:interp u sch). root_model u sch i) =
  let uf : symbols u sch = {
    apply = (fun f _ -> S.value_inhabitant sch (default_value u) f.range);
    lambda = (fun bound t _ -> S.value_inhabitant sch (default_value u) (ArraySort bound t));
  } in
  lemma_standard_root u sch uf

(* ---------------------------------------------------------------------- *)
(* Evaluation step for interpreted applications (used by the AST witnesses) *)
(* ---------------------------------------------------------------------- *)

let lemma_eval_interpreted (u:uninterpreted) (sch:S.checked_schema) (uf:symbols u sch)
                           (scope:list sort) (rho:V.environment (carrier u) (S.signature sch) scope)
                           (f:func_decl) (args:list expr)
  : Lemma (requires D.scoped scope (App f args) /\ not (datatype_kind f) /\
                    Some? (interpreted u sch f
                      (V.evaluate_args (S.signature sch) (standard u sch uf) scope rho args f.domain)))
          (ensures V.evaluate (S.signature sch) (standard u sch uf) scope rho (App f args) ==
                   Some?.v (interpreted u sch f
                     (V.evaluate_args (S.signature sch) (standard u sch uf) scope rho args f.domain))) =
  lemma_not_constructor sch f;
  lemma_standard_application u sch uf f
    (V.evaluate_args (S.signature sch) (standard u sch uf) scope rho args f.domain)

let lemma_eval_free_choice (u:uninterpreted) (sch:S.checked_schema) (uf:symbols u sch)
                           (scope:list sort) (rho:V.environment (carrier u) (S.signature sch) scope)
                           (f:func_decl) (args:list expr)
  : Lemma (requires D.scoped scope (App f args) /\ not (datatype_kind f) /\
                    None? (interpreted u sch f
                      (V.evaluate_args (S.signature sch) (standard u sch uf) scope rho args f.domain)))
          (ensures V.evaluate (S.signature sch) (standard u sch uf) scope rho (App f args) ==
                   uf.apply f (V.evaluate_args (S.signature sch) (standard u sch uf) scope rho args f.domain)) =
  lemma_not_constructor sch f;
  lemma_standard_application u sch uf f
    (V.evaluate_args (S.signature sch) (standard u sch uf) scope rho args f.domain)

(* Function-space facts behind the array laws (no hypothesis). *)
let lemma_read_write_same (#a #b:Type0) (fn:func_space a b) (i:a) (v:b)
  : Lemma (read (write fn i v) i == v) = ()

let lemma_read_write_other (#a #b:Type0) (fn:func_space a b) (i j:a) (v:b)
  : Lemma (requires ~(j == i)) (ensures read (write fn i v) j == read fn j) = ()

let lemma_function_extensionality (#a #b:Type0) (fn gn:func_space a b)
  : Lemma ((forall (x:a). read fn x == read gn x) <==> fn == gn) =
  FE.extensionality_g a (fun _ -> b) fn gn

(* Evaluation of production quantifier nodes under the standard model. *)
let lemma_eval_forall (u:uninterpreted) (sch:S.checked_schema) (uf:symbols u sch)
                      (scope:list sort) (rho:V.environment (carrier u) (S.signature sch) scope)
                      (bound:list sort) (body:expr)
  : Lemma (requires D.scoped scope (Quantifier Forall_k bound bool_sort body))
          (ensures truth sch (V.evaluate (S.signature sch) (standard u sch uf) scope rho
                               (Quantifier Forall_k bound bool_sort body)) == true <==>
                   (forall (vs:targuments u sch (L.rev bound)).
                      truth sch (V.evaluate (S.signature sch) (standard u sch uf) (L.rev bound @ scope)
                                   (V.extend (S.signature sch) scope (L.rev bound) vs rho) body) == true)) =
  let sigma = S.signature sch in
  let fbody = V.typed_body sigma bound bool_sort
                (V.evaluate_body sigma (standard u sch uf) scope rho bound body) in
  lemma_forall_case u sch uf bound fbody

let lemma_eval_exists (u:uninterpreted) (sch:S.checked_schema) (uf:symbols u sch)
                      (scope:list sort) (rho:V.environment (carrier u) (S.signature sch) scope)
                      (bound:list sort) (body:expr)
  : Lemma (requires D.scoped scope (Quantifier Exists_k bound bool_sort body))
          (ensures truth sch (V.evaluate (S.signature sch) (standard u sch uf) scope rho
                               (Quantifier Exists_k bound bool_sort body)) == true <==>
                   (exists (vs:targuments u sch (L.rev bound)).
                      truth sch (V.evaluate (S.signature sch) (standard u sch uf) (L.rev bound @ scope)
                                   (V.extend (S.signature sch) scope (L.rev bound) vs rho) body) == true)) =
  let sigma = S.signature sch in
  let fbody = V.typed_body sigma bound bool_sort
                (V.evaluate_body sigma (standard u sch uf) scope rho bound body) in
  lemma_exists_case u sch uf bound fbody

(* A lambda at a supported sort evaluates to the graph of its body; reading
   the graph at an index tuple evaluates the body under the REVERSED typed
   arguments (innermost binder = last index). *)
let lemma_eval_lambda (u:uninterpreted) (sch:S.checked_schema) (uf:symbols u sch)
                      (scope:list sort) (rho:V.environment (carrier u) (S.signature sch) scope)
                      (bound:list sort) (t:sort) (body:expr)
                      (ix:indices u bound)
  : Lemma (requires D.scoped scope (Quantifier Lambda_k bound (ArraySort bound t) body) /\
                    get_sort body == t /\ free (S.signature sch) (ArraySort bound t))
          (ensures read #(indices u bound) #(carrier u t)
                     (scalar #u #(S.signature sch) (ArraySort bound t)
                       (V.evaluate (S.signature sch) (standard u sch uf) scope rho
                         (Quantifier Lambda_k bound (ArraySort bound t) body))) ix ==
                   scalar #u #(S.signature sch) t
                     (V.evaluate (S.signature sch) (standard u sch uf) (L.rev bound @ scope)
                       (V.extend (S.signature sch) scope (L.rev bound)
                         (reverse_arguments (S.signature sch) bound
                           (from_indices #u #(S.signature sch) bound ix)) rho) body)) =
  ()

(* ---------------------------------------------------------------------- *)
(* Expression-level array laws at every supported single-index sort,       *)
(* derived from the standard model (not assumed)                            *)
(* ---------------------------------------------------------------------- *)

let lemma_classify_select (sigma:V.signature) (ds:list sort) (r:sort)
  : Lemma (requires free sigma (ArraySort ds r))
          (ensures classify sigma (select_decl ds r) == Select ds r) = ()

let lemma_classify_store (sigma:V.signature) (ds:list sort) (r:sort)
  : Lemma (requires free sigma (ArraySort ds r))
          (ensures classify sigma (store_decl ds r) == Store ds r) = ()

let lemma_store_value (u:uninterpreted) (sch:S.checked_schema) (d r:sort)
                      (va:tvalue u sch (ArraySort [d] r)) (vi:tvalue u sch d) (vv:tvalue u sch r)
  : Lemma (requires free (S.signature sch) (ArraySort [d] r))
          (ensures Some? (interpreted u sch (store_decl [d] r) [va; vi; vv]) /\
                   Some?.v (interpreted u sch (store_decl [d] r) [va; vi; vv]) ==
                   make #u #(S.signature sch) (ArraySort [d] r)
                     (write #(indices u [d]) #(carrier u r) (scalar #u #(S.signature sch) (ArraySort [d] r) va)
                       (to_indices #u #(S.signature sch) [d] [vi]) (scalar #u #(S.signature sch) r vv))) =
  lemma_classify_store (S.signature sch) [d] r

let lemma_select_value (u:uninterpreted) (sch:S.checked_schema) (d r:sort)
                       (va:tvalue u sch (ArraySort [d] r)) (vi:tvalue u sch d)
  : Lemma (requires free (S.signature sch) (ArraySort [d] r))
          (ensures Some? (interpreted u sch (select_decl [d] r) [va; vi]) /\
                   Some?.v (interpreted u sch (select_decl [d] r) [va; vi]) ==
                   make #u #(S.signature sch) r
                     (read #(indices u [d]) #(carrier u r) (scalar #u #(S.signature sch) (ArraySort [d] r) va)
                       (to_indices #u #(S.signature sch) [d] [vi]))) =
  lemma_classify_select (S.signature sch) [d] r

let lemma_eval_store (u:uninterpreted) (sch:S.checked_schema) (uf:symbols u sch)
                     (scope:list sort) (rho:V.environment (carrier u) (S.signature sch) scope)
                     (d r:sort) (a i v:expr)
  : Lemma (requires free (S.signature sch) (ArraySort [d] r) /\ D.scoped scope (App (store_decl [d] r) [a; i; v]) /\
                    get_sort a == ArraySort [d] r /\ get_sort i == d /\ get_sort v == r)
          (ensures (let ev (e:expr{D.scoped scope e}) = V.evaluate (S.signature sch) (standard u sch uf) scope rho e in
                    ev (App (store_decl [d] r) [a; i; v]) ==
                    make #u #(S.signature sch) (ArraySort [d] r)
                      (write #(indices u [d]) #(carrier u r) (scalar #u #(S.signature sch) (ArraySort [d] r) (ev a))
                        (to_indices #u #(S.signature sch) [d] [ev i]) (scalar #u #(S.signature sch) r (ev v))))) =
  let sigma = S.signature sch in
  let ev (e:expr{D.scoped scope e}) = V.evaluate sigma (standard u sch uf) scope rho e in
  assert (V.evaluate_args sigma (standard u sch uf) scope rho [a; i; v] (store_decl [d] r).domain ==
          [ev a; ev i; ev v]);
  lemma_store_value u sch d r (ev a) (ev i) (ev v);
  lemma_eval_interpreted u sch uf scope rho (store_decl [d] r) [a; i; v]

let lemma_eval_select (u:uninterpreted) (sch:S.checked_schema) (uf:symbols u sch)
                      (scope:list sort) (rho:V.environment (carrier u) (S.signature sch) scope)
                      (d r:sort) (a i:expr)
  : Lemma (requires free (S.signature sch) (ArraySort [d] r) /\ D.scoped scope (App (select_decl [d] r) [a; i]) /\
                    get_sort a == ArraySort [d] r /\ get_sort i == d)
          (ensures (let ev (e:expr{D.scoped scope e}) = V.evaluate (S.signature sch) (standard u sch uf) scope rho e in
                    ev (App (select_decl [d] r) [a; i]) ==
                    make #u #(S.signature sch) r
                      (read #(indices u [d]) #(carrier u r) (scalar #u #(S.signature sch) (ArraySort [d] r) (ev a))
                        (to_indices #u #(S.signature sch) [d] [ev i])))) =
  let sigma = S.signature sch in
  let ev (e:expr{D.scoped scope e}) = V.evaluate sigma (standard u sch uf) scope rho e in
  assert (V.evaluate_args sigma (standard u sch uf) scope rho [a; i] (select_decl [d] r).domain == [ev a; ev i]);
  lemma_select_value u sch d r (ev a) (ev i);
  lemma_eval_interpreted u sch uf scope rho (select_decl [d] r) [a; i]

(* select (store a i v) i = v, for every supported single-index array sort *)
let lemma_select_store_same (u:uninterpreted) (sch:S.checked_schema) (uf:symbols u sch)
                            (scope:list sort) (rho:V.environment (carrier u) (S.signature sch) scope)
                            (d r:sort) (a i v:expr)
  : Lemma (requires free (S.signature sch) (ArraySort [d] r) /\
                    D.scoped scope (App (select_decl [d] r) [App (store_decl [d] r) [a; i; v]; i]) /\
                    get_sort a == ArraySort [d] r /\ get_sort i == d /\ get_sort v == r)
          (ensures V.evaluate (S.signature sch) (standard u sch uf) scope rho
                     (App (select_decl [d] r) [App (store_decl [d] r) [a; i; v]; i]) ==
                   V.evaluate (S.signature sch) (standard u sch uf) scope rho v) =
  let sigma = S.signature sch in
  let ev (e:expr{D.scoped scope e}) = V.evaluate sigma (standard u sch uf) scope rho e in
  let st = App (store_decl [d] r) [a; i; v] in
  lemma_eval_store u sch uf scope rho d r a i v;
  lemma_eval_select u sch uf scope rho d r st i;
  let fa = scalar #u #sigma (ArraySort [d] r) (ev a) in
  let ix = to_indices #u #sigma [d] [ev i] in
  lemma_read_write_same #(indices u [d]) #(carrier u r) fa ix (scalar #u #sigma r (ev v));
  lemma_make_scalar #u #sigma r (ev v)

(* i <> j  ==>  select (store a i v) j = select a j *)
let lemma_select_store_other (u:uninterpreted) (sch:S.checked_schema) (uf:symbols u sch)
                             (scope:list sort) (rho:V.environment (carrier u) (S.signature sch) scope)
                             (d r:sort) (a i j v:expr)
  : Lemma (requires free (S.signature sch) (ArraySort [d] r) /\
                    D.scoped scope (App (select_decl [d] r) [App (store_decl [d] r) [a; i; v]; j]) /\
                    D.scoped scope (App (select_decl [d] r) [a; j]) /\
                    get_sort a == ArraySort [d] r /\ get_sort i == d /\ get_sort j == d /\ get_sort v == r /\
                    ~(V.evaluate (S.signature sch) (standard u sch uf) scope rho i ==
                      V.evaluate (S.signature sch) (standard u sch uf) scope rho j))
          (ensures V.evaluate (S.signature sch) (standard u sch uf) scope rho
                     (App (select_decl [d] r) [App (store_decl [d] r) [a; i; v]; j]) ==
                   V.evaluate (S.signature sch) (standard u sch uf) scope rho
                     (App (select_decl [d] r) [a; j])) =
  let sigma = S.signature sch in
  let ev (e:expr{D.scoped scope e}) = V.evaluate sigma (standard u sch uf) scope rho e in
  let st = App (store_decl [d] r) [a; i; v] in
  lemma_eval_store u sch uf scope rho d r a i v;
  lemma_eval_select u sch uf scope rho d r st j;
  lemma_eval_select u sch uf scope rho d r a j;
  lemma_make_scalar #u #sigma d (ev i);
  lemma_make_scalar #u #sigma d (ev j);
  let fa = scalar #u #sigma (ArraySort [d] r) (ev a) in
  lemma_read_write_other #(indices u [d]) #(carrier u r) fa
    (to_indices #u #sigma [d] [ev i]) (to_indices #u #sigma [d] [ev j]) (scalar #u #sigma r (ev v))

(* Extensionality of array VALUES at every supported sort (any arity). *)
let lemma_array_extensionality (#u:uninterpreted) (#sigma:V.signature) (ds:list sort) (r:sort)
                               (x y:V.value (carrier u) sigma (ArraySort ds r))
  : Lemma (requires free sigma (ArraySort ds r))
          (ensures x == y <==>
                   (forall (ix:indices u ds).
                      read #(indices u ds) #(carrier u r) (scalar #u #sigma (ArraySort ds r) x) ix ==
                      read #(indices u ds) #(carrier u r) (scalar #u #sigma (ArraySort ds r) y) ix)) =
  lemma_function_extensionality #(indices u ds) #(carrier u r)
    (scalar #u #sigma (ArraySort ds r) x) (scalar #u #sigma (ArraySort ds r) y);
  lemma_make_scalar #u #sigma (ArraySort ds r) x;
  lemma_make_scalar #u #sigma (ArraySort ds r) y

(* The array-ext difference witness, by the library's ghost indefinite
   description (no new axiom). Not yet wired to the array-ext operator. *)
let difference (#a #b:Type0) (fn gn:func_space a b) (fallback:a)
  : GTot (x:a{fn == gn \/ ~(read fn x == read gn x)}) =
  if decide (fn == gn) then fallback
  else begin
    lemma_function_extensionality fn gn;
    ID.indefinite_description_ghost a (fun ix -> ~(read fn ix == read gn ix))
  end

let lemma_difference (#a #b:Type0) (fn gn:func_space a b) (fallback:a)
  : Lemma (fn == gn \/ ~(read fn (difference fn gn fallback) == read gn (difference fn gn fallback))) = ()
