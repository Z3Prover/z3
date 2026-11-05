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
   supported domain: their carrier is a nonempty PLACEHOLDER. On it, select,
   store, lambda and every other array/theory symbol are free model choices
   with no array law, but `=`, `ite` and forall/exists are still interpreted
   (equality, choice and quantification over the placeholder carrier). That
   is sound (L1), but has no SMT meaning, so `supported_expression` rejects
   every term that mentions such a sort. Zero-index arrays (ArraySort [] r,
   at any depth) have a carrier and satisfy the array laws below, but are
   not SMT-LIB sorts and are likewise rejected by the support checks.

   Interpreted operators (canonical metadata only, see `classify`): true, false,
   not, =>, n-ary and/or/xor, = at every sort, ite at every sort, Int and Real
   numerals (op_num_rational), + * - over Int or Real (n-ary, including the
   native binary Int op_plus/op_mul records; nullary + and * are the empty
   sum 0 and empty product 1: at Int exactly as Z3SortedInteger.classify
   computes them, at Real by R2 through i itself, because the Sorted layers
   classify no Real operator), Real / with a nonzero
   divisor, to_real, <= < >= > over Int or Real, select and store at every
   datatype-free array sort (any arity, nested), lambda at every
   datatype-free array sort, forall/exists over every sort. Everything else
   is a free choice in `symbols` (uninterpreted symbols, Int div/mod/abs,
   distinct, const-array, array-ext, BV/FF/Seq/FP operators, real division
   by zero, ill-matched datatype selectors, and select/store/lambda at array
   sorts mentioning a datatype).

   Contract (corrected): `root_model` = R1 quantifiers, R2 operators (single
   definitional source `interpreted`), R3 lambdas, R4 constructors, R5
   recognizers (constructor identity, via S.find_recognizer), R6 matched
   accessors (exact field, via S.find_accessor; unmatched selectors stay free).
   Kernels use the NAMED laws (the law_ and lemma_eval_ lemmas), proved for
   EVERY model of root_model, never the definition of `interpreted` or `standard`.

   L1 `lemma_standard_root`: `standard u sch uf` satisfies root_model for EVERY
   u and uf over every checked schema (constructibility). The STANDARD (SMT)
   meaning is claimed only for `supported` schemas and expressions passing
   `supported_expression`; both are pure executable checks that no production
   route enforces in G1. Front-end obligation (not checked here): BaseSort
   "Bool"/"Int"/"Real" in the AST denote the SMT theory sorts. *)

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

(* A sort is datatype-free (standard carrier, theory laws apply) iff it
   mentions no datatype sort of the schema. Executable, structural,
   schema-dependent. `supported_sort` below also admits datatype sorts
   themselves (checked constructor trees). *)
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
   zero, ill-matched datatype selectors, and select/store/lambda (and every
   other non-connective operator) at an array sort mentioning a datatype.
   `=` and `ite` at such a placeholder sort are NOT free: they are
   interpreted by `connective` like at every other sort. *)
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

(* Same tests as Z3SortedSemantics.classify (a root-local copy, so that this
   module depends on no Sorted module). The copies cannot drift silently:
   Z3SortedRoot.lemma_core_agreement proves them equal on every declaration
   (TR.connective f == core_op (T.classify f)) and fails to verify if
   either copy changes. *)
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

(* Numerals, arithmetic, to_real and comparisons. Nullary policy (G2
   preparation, a deliberate change of the root class): a nullary canonical
   `+`/`*` (op_arith_add/op_arith_mul, no parameters) is NOT a numeral, so it
   reaches `A.operation_of` and classifies as the empty sum (0) / empty
   product (1). At Int this is exactly what Z3SortedInteger.classify
   computes at runtime; at Real the Sorted layers classify nothing (Sorted
   passes the record to i, where R2 gives 0.0 / 1.0).
   Before this change TR left it free. Z3 itself rejects nullary arithmetic
   operators (arith_decl_plugin::mk_func_decl, "no arguments supplied to
   arithmetical operator"), so no SMT-LIB/native term is affected: the change
   only narrows the root class on non-SMT input and is no coverage gain.
   Nullary `-` stays Other (operation_of needs an argument). *)
let numeric (sigma:V.signature) (f:func_decl) : theory_op =
  let s = f.range in
  if (s = int_s || s = real_s) && not (V.datatype_sort sigma s) && f.domain = [] &&
     Some? (A.numeral (App f [])) then
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
(* Supported domain: schemas, sorts and expressions (pure, executable)      *)
(* ---------------------------------------------------------------------- *)

let rec base_owned (sigma:V.signature) : Tot bool (decreases sigma) =
  match sigma with [] -> true | f :: rest -> BaseSort? f.range && base_owned rest

(* SMT-LIB shape of a sort: every array sort, at ANY depth (index sorts and
   result sort), has at least one index. `ArraySort [] r` has a carrier
   (functions from unit) and the array laws below hold for it, but it is not
   an SMT-LIB sort, so the coverage checks exclude it. *)
let rec smt_shaped (s:sort) : Tot bool (decreases s) =
  match s with
  | BaseSort _ -> true
  | ArraySort ds r -> Cons? ds && smt_shaped_all ds && smt_shaped r

and smt_shaped_all (ss:list sort) : Tot bool (decreases ss) =
  match ss with [] -> true | s :: rest -> smt_shaped s && smt_shaped_all rest

(* Sort part: an SMT-shaped sort that is a datatype sort itself (values are
   checked constructor trees) or mentions no datatype (standard carrier).
   Rejected: array sorts whose index or result (at any depth) mentions a
   registered datatype (they only have a nonempty PLACEHOLDER carrier and no
   array law), and zero-index arrays at any depth. *)
let supported_sort (sigma:V.signature) (s:sort) : bool =
  smt_shaped s && (V.datatype_sort sigma s || free sigma s)

let rec supported_sorts (sigma:V.signature) (ss:list sort) : Tot bool (decreases ss) =
  match ss with [] -> true | s :: rest -> supported_sort sigma s && supported_sorts sigma rest

(* Every constructor field of the schema is a supported sort (the root's
   OWN coverage check on fields; S.valid's supported_fields does not reject
   zero-index arrays). *)
let rec fields_supported (sigma:V.signature) (cs:list S.constructor_case) : Tot bool (decreases cs) =
  match cs with
  | [] -> true
  | c :: rest -> supported_sorts sigma c.S.constructor.domain && fields_supported sigma rest

(* Schema part of the claimed STANDARD domain, as an executable check:
   S.valid (cases, recognizers, accessors, distinct cases, productive sorts,
   no Bool/Int datatype), no datatype registered under the name "Real",
   no array-ranged constructor, and supported constructor fields.
   Constructibility (L1) does not need it: a root model exists for every
   checked schema, but on an unsupported schema primitive Real heads
   (numerals, +, /, ...) classify as free symbols, so the root class there
   is NOT an SMT semantics class. No production route enforces this check;
   a future root validator must establish it (it is not implied by S.valid). *)
let supported (sch:S.schema) : bool =
  S.valid sch && not (V.datatype_sort (S.signature sch) real_s) && base_owned (S.signature sch) &&
  fields_supported (S.signature sch) sch.S.cases

type supported_schema = sch:S.checked_schema{supported sch}

(* Expression part: EVERY sort occurring in the term (variable sorts, the
   domain and range of every declaration, every binder sort and every
   quantifier/lambda sort, at every depth) is supported. So an unsupported
   nested subterm cannot hide inside an opaque leaf and then receive a
   theory law. This is a COVERAGE check, not a typing check: it does not
   test that a Var's sort label matches its binder, nor argument/domain
   agreement. Any future L2 must combine it with D.scoped (and the
   document's own well-formedness checks) on the real document; it is a
   PURE, future-checkable interface that no route or validator calls yet. *)
let rec supported_expression (sigma:V.signature) (e:expr) : Tot bool (decreases e) =
  match e with
  | Var _ s -> supported_sort sigma s
  | App f args ->
    supported_sort sigma f.range && supported_sorts sigma f.domain && supported_expressions sigma args
  | Quantifier _ bound s body ->
    supported_sorts sigma bound && supported_sort sigma s && supported_expression sigma body

and supported_expressions (sigma:V.signature) (es:list expr) : Tot bool (decreases es) =
  match es with [] -> true | e :: rest -> supported_expression sigma e && supported_expressions sigma rest

(* A whole query/document: every expression supported over a supported schema. *)
let supported_document (sch:S.schema) (es:list expr) : bool =
  supported sch && supported_expressions (S.signature sch) es

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

(* R4: constructors build the checked constructor trees. (The evaluator
   builds registered constructors itself, V.evaluate's App case; R4 makes
   the interpretation's own application agree with that layer.) *)
let constructor_law (u:uninterpreted) (sch:S.checked_schema) (i:interp u sch) : prop =
  forall (f:func_decl{L.mem f (S.signature sch)}) (xs:targuments u sch f.domain).
    i.application f xs == V.construct (S.signature sch) f xs

(* R5: a recognizer of the schema, as found by the executable metadata
   search S.find_recognizer, tests constructor identity: is-c(v) is true
   exactly when the head constructor of the checked tree v is c's
   constructor (V.recognize is that head test, not the standard model). *)
let recognizer_case (u:uninterpreted) (sch:S.checked_schema) (i:interp u sch) (f:func_decl)
                    (c:S.constructor_case{L.mem c sch.cases /\ f.domain = [c.constructor.range] /\
                                          f.range = bool_sort})
                    (v:tvalue u sch c.constructor.range) : prop =
  truth sch (i.application f [v]) == V.recognize c.constructor v

let recognizer_at (u:uninterpreted) (sch:S.checked_schema) (i:interp u sch) (f:func_decl) : prop =
  match S.find_recognizer f sch.cases with
  | None -> True
  | Some c -> (forall (v:tvalue u sch c.constructor.range). recognizer_case u sch i f c v)

let recognizer_law (u:uninterpreted) (sch:S.checked_schema) (i:interp u sch) : prop =
  forall (f:func_decl). recognizer_at u sch i f

(* The n-th field of a typed argument list, at its declared sort. *)
let field_of (#u:uninterpreted) (#sch:S.checked_schema) (ss:list sort) (ys:targuments u sch ss)
             (n:nat{n < L.length ss}) : tvalue u sch (L.index ss n) =
  V.lemma_fields_index (S.signature sch) ss ys n;
  L.index ys n

type accessor_of (sch:S.checked_schema) (f:func_decl) =
  r:S.accessor_match{L.mem r.matched_case sch.cases /\
                     r.field < L.length r.matched_case.constructor.domain /\
                     f.domain = [r.matched_case.constructor.range] /\
                     f.range = L.index r.matched_case.constructor.domain r.field}

(* R6: a MATCHED selector (S.find_accessor gives its case c and field n)
   applied to a c-constructed tree returns exactly its n-th field. Nothing
   is said about a selector applied to a tree of another constructor: that
   value stays an arbitrary, argument-dependent free choice. *)
let accessor_case (u:uninterpreted) (sch:S.checked_schema) (i:interp u sch) (f:func_decl)
                  (r:accessor_of sch f) (ys:targuments u sch r.matched_case.constructor.domain) : prop =
  i.application f [S.constructor_value sch r.matched_case ys] ==
  field_of #u #sch r.matched_case.constructor.domain ys r.field

let accessor_at (u:uninterpreted) (sch:S.checked_schema) (i:interp u sch) (f:func_decl) : prop =
  match S.find_accessor f sch.cases with
  | None -> True
  | Some r -> (forall (ys:targuments u sch r.matched_case.constructor.domain). accessor_case u sch i f r ys)

let accessor_law (u:uninterpreted) (sch:S.checked_schema) (i:interp u sch) : prop =
  forall (f:func_decl). accessor_at u sch i f

(* The corrected root contract: R1-R6, one joint interpretation. *)
let root_model (u:uninterpreted) (sch:S.checked_schema) (i:interp u sch) : prop =
  quantifier_laws u sch i /\ operator_law u sch i /\ lambda_law u sch i /\ constructor_law u sch i /\
  recognizer_law u sch i /\ accessor_law u sch i

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

(* Metadata facts: the three datatype kinds are told apart by their interp
   tag, so a recognizer or an accessor is never a registered constructor,
   and an accessor is never a recognizer. *)
let lemma_constructor_interp (sch:S.checked_schema) (f:func_decl)
  : Lemma (requires L.mem f (S.signature sch)) (ensures f.interp == Some Z3DatatypeLemma.op_constructor) =
  S.lemma_case_of sch.cases f;
  let c = Some?.v (S.case_of sch.cases f) in
  S.lemma_case_member (S.signature sch) sch.sorts sch.cases c

let rec lemma_recognizer_interp (f:func_decl) (cs:list S.constructor_case)
  : Lemma (requires Some? (S.find_recognizer f cs))
          (ensures f.interp == Some Z3DatatypeLemma.op_recognizer) (decreases cs) =
  match cs with
  | [] -> ()
  | c :: rest -> if Some? (S.find_recognizer f rest) then lemma_recognizer_interp f rest

let rec lemma_accessor_interp (f:func_decl) (cs:list S.constructor_case)
  : Lemma (requires Some? (S.find_accessor f cs))
          (ensures f.interp == Some Z3DatatypeLemma.op_accessor) (decreases cs) =
  match cs with
  | [] -> ()
  | c :: rest -> if Some? (S.find_accessor f rest) then lemma_accessor_interp f rest

let lemma_recognizer_at (u:uninterpreted) (sch:S.checked_schema) (uf:symbols u sch) (f:func_decl)
  : Lemma (recognizer_at u sch (standard u sch uf) f) =
  match S.find_recognizer f sch.cases with
  | None -> ()
  | Some c ->
    lemma_recognizer_interp f sch.cases;
    if L.mem f (S.signature sch) then lemma_constructor_interp sch f

let lemma_recognizer_law (u:uninterpreted) (sch:S.checked_schema) (uf:symbols u sch)
  : Lemma (recognizer_law u sch (standard u sch uf)) =
  FStar.Classical.forall_intro (lemma_recognizer_at u sch uf)

let lemma_accessor_at (u:uninterpreted) (sch:S.checked_schema) (uf:symbols u sch) (f:func_decl)
  : Lemma (accessor_at u sch (standard u sch uf) f) =
  match S.find_accessor f sch.cases with
  | None -> ()
  | Some r ->
    lemma_accessor_interp f sch.cases;
    if L.mem f (S.signature sch) then lemma_constructor_interp sch f;
    if Some? (S.find_recognizer f sch.cases) then lemma_recognizer_interp f sch.cases;
    let c = r.matched_case in
    let aux (ys:targuments u sch c.constructor.domain)
      : Lemma (accessor_case u sch (standard u sch uf) f r ys) =
      S.lemma_signature_member sch.cases c;
      V.lemma_fields_index (S.signature sch) c.constructor.domain ys r.field in
    FStar.Classical.forall_intro aux

let lemma_accessor_law (u:uninterpreted) (sch:S.checked_schema) (uf:symbols u sch)
  : Lemma (accessor_law u sch (standard u sch uf)) =
  FStar.Classical.forall_intro (lemma_accessor_at u sch uf)

(* L1. No hypothesis on u or uf: one joint positive model of the CORRECTED
   contract R1-R6 for every free choice. Constructibility holds for every
   checked schema (`supported` is not needed for it); the STANDARD meaning
   of the root class is claimed only on supported schemas and supported
   expressions (see the support section and the law preconditions). *)
let lemma_standard_root (u:uninterpreted) (sch:S.checked_schema) (uf:symbols u sch)
  : Lemma (root_model u sch (standard u sch uf)) =
  lemma_quantifier_laws u sch uf;
  lemma_operator_law u sch uf;
  lemma_lambda_law u sch uf;
  lemma_constructor_law u sch uf;
  lemma_recognizer_law u sch uf;
  lemma_accessor_law u sch uf

(* Non-vacuity: the class of root models is inhabited for every checked
   schema and every choice of uninterpreted carriers. *)
let lemma_root_inhabited (u:uninterpreted) (sch:S.checked_schema)
  : Lemma (exists (i:interp u sch). root_model u sch i) =
  let uf : symbols u sch = {
    apply = (fun f _ -> S.value_inhabitant sch (default_value u) f.range);
    lambda = (fun bound t _ -> S.value_inhabitant sch (default_value u) (ArraySort bound t));
  } in
  lemma_standard_root u sch uf

(* ---------------------------------------------------------------------- *)
(* Free choices of the standard family (standard-specific, by design)      *)
(* ---------------------------------------------------------------------- *)

(* In the standard family an application that SMT-LIB leaves open (an
   operator outside the interpreted set, a real division by zero, an
   unmatched selector at the theory layer) is exactly the free choice. *)
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

(* ---------------------------------------------------------------------- *)
(* Function-space facts behind the array laws (no hypothesis)               *)
(* ---------------------------------------------------------------------- *)

let lemma_read_write_same (#a #b:Type0) (fn:func_space a b) (i:a) (v:b)
  : Lemma (read (write fn i v) i == v) = ()

let lemma_read_write_other (#a #b:Type0) (fn:func_space a b) (i j:a) (v:b)
  : Lemma (requires ~(j == i)) (ensures read (write fn i v) j == read fn j) = ()

let lemma_function_extensionality (#a #b:Type0) (fn gn:func_space a b)
  : Lemma ((forall (x:a). read fn x == read gn x) <==> fn == gn) =
  FE.extensionality_g a (fun _ -> b) fn gn

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
   description (no new axiom). Not wired to the array-ext operator, which
   stays a FREE symbol in this correction. *)
let difference (#a #b:Type0) (fn gn:func_space a b) (fallback:a)
  : GTot (x:a{fn == gn \/ ~(read fn x == read gn x)}) =
  if decide (fn == gn) then fallback
  else begin
    lemma_function_extensionality fn gn;
    ID.indefinite_description_ghost a (fun ix -> ~(read fn ix == read gn ix))
  end

let lemma_difference (#a #b:Type0) (fn gn:func_space a b) (fallback:a)
  : Lemma (fn == gn \/ ~(read fn (difference fn gn fallback) == read gn (difference fn gn fallback))) = ()

(* ====================================================================== *)
(* NAMED LAWS, proved for EVERY model i of root_model (not only standard).  *)
(* Each law is stated with the executable classifier fact that identifies  *)
(* the operator (or the canonical array declaration) as its precondition   *)
(* and the expected mathematical value (F* bool/int/FStar.Real operators,  *)
(* typed argument lists, constructor trees) as its conclusion. Kernels     *)
(* cite these laws; they never need to unfold `interpreted`/`standard`.    *)
(* Operators outside this list (distinct, op_num_int numerals, Int         *)
(* div/mod/abs, to_int/is_int, const-array, array-ext, op_oeq, n-ary =,    *)
(* n-ary =>, BV/FF/Seq/FP/String/Regex, real x/0, unmatched selectors,     *)
(* select/store/lambda at array sorts mentioning a datatype) are FREE: no  *)
(* law is claimed. Some laws (law_equality, law_ite, R1) also hold at such *)
(* placeholder sorts, but with no SMT meaning there: the support checks   *)
(* exclude those terms. The preconditions of each law are stated in it    *)
(* (domain shape, supported_schema, free array sort, nonzero divisor,      *)
(* distinct index tuples), not only the classifier fact.                   *)
(* ====================================================================== *)

(* Every classified (non-Other) operator carries a theory interp tag, so it
   is never a datatype operation and never a registered constructor. *)
let lemma_connective_theory (f:func_decl)
  : Lemma (requires ~(Other? (connective f))) (ensures not (datatype_kind f)) = ()

let lemma_numeric_theory (sigma:V.signature) (f:func_decl)
  : Lemma (requires ~(Other? (numeric sigma f))) (ensures not (datatype_kind f)) = ()

let lemma_array_theory (sigma:V.signature) (f:func_decl)
  : Lemma (requires ~(Other? (array_op sigma f))) (ensures not (datatype_kind f)) = ()

let lemma_classified_theory (sch:S.checked_schema) (f:func_decl)
  : Lemma (requires ~(Other? (classify (S.signature sch) f)))
          (ensures not (datatype_kind f) /\ not (L.mem f (S.signature sch))) =
  let sigma = S.signature sch in
  (if not (Other? (connective f)) then lemma_connective_theory f
   else if not (Other? (numeric sigma f)) then lemma_numeric_theory sigma f
   else lemma_array_theory sigma f);
  lemma_not_constructor sch f

(* The single use of R2 (internal: the laws below are the interface). *)
let lemma_operator (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch)
                   (f:func_decl) (xs:targuments u sch f.domain)
  : Lemma (requires root_model u sch i /\ ~(Other? (classify (S.signature sch) f)) /\
                    Some? (interpreted u sch f xs))
          (ensures i.application f xs == Some?.v (interpreted u sch f xs)) =
  lemma_classified_theory sch f

(* Primitive values of a tree. Int is never a datatype of a checked schema
   (S.valid); Real is not a datatype of a supported schema. *)
let int_of (#u:uninterpreted) (sch:S.checked_schema) (v:tvalue u sch int_s) : int =
  scalar #u #(S.signature sch) int_s v

let real_of (#u:uninterpreted) (sch:supported_schema) (v:tvalue u sch real_s) : real =
  scalar #u #(S.signature sch) real_s v

(* --- Boolean connectives ------------------------------------------------- *)

let law_constant (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch) (f:func_decl) (b:bool)
                 (xs:targuments u sch f.domain)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Constant b)
          (ensures truth sch (i.application f xs) == b) =
  lemma_operator i f xs

let law_not (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch) (f:func_decl)
            (x:tvalue u sch bool_sort)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Negation)
          (ensures truth sch (i.application f [x]) == not (truth sch x)) =
  lemma_operator i f [x]

let law_implies (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch) (f:func_decl)
                (x y:tvalue u sch bool_sort)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Implication)
          (ensures truth sch (i.application f [x; y]) == (not (truth sch x) || truth sch y)) =
  lemma_operator i f [x; y]

let law_and (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch) (f:func_decl)
            (x y:tvalue u sch bool_sort)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Nary B.And /\
                    f.domain == [bool_sort; bool_sort])
          (ensures truth sch (i.application f [x; y]) == (truth sch x && truth sch y)) =
  lemma_operator i f [x; y]

let law_or (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch) (f:func_decl)
           (x y:tvalue u sch bool_sort)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Nary B.Or /\
                    f.domain == [bool_sort; bool_sort])
          (ensures truth sch (i.application f [x; y]) == (truth sch x || truth sch y)) =
  lemma_operator i f [x; y]

let law_xor (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch) (f:func_decl)
            (x y:tvalue u sch bool_sort)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Nary B.Xor /\
                    f.domain == [bool_sort; bool_sort])
          (ensures truth sch (i.application f [x; y]) == (truth sch x <> truth sch y)) =
  lemma_operator i f [x; y]

(* n-ary and/or/xor: the fold of the production Boolean semantics
   (B.combine/B.neutral), i.e. conjunction, disjunction, parity. *)
let law_nary (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch) (f:func_decl) (op:B.nary_op)
             (xs:targuments u sch f.domain)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Nary op)
          (ensures truth sch (i.application f xs) == combine op (truths sch f.domain xs)) =
  lemma_operator i f xs

let rec lemma_combine_and (bs:list bool)
  : Lemma (combine B.And bs == true <==> (forall (b:bool). L.mem b bs ==> b)) (decreases bs) =
  match bs with [] -> () | _ :: rest -> lemma_combine_and rest

let rec lemma_combine_or (bs:list bool)
  : Lemma (combine B.Or bs == true <==> L.mem true bs) (decreases bs) =
  match bs with [] -> () | _ :: rest -> lemma_combine_or rest

(* --- Equality and if-then-else at every sort --------------------------- *)

let law_equality (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch) (f:func_decl) (s:sort)
                 (x y:tvalue u sch s)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Equality s)
          (ensures truth sch (i.application f [x; y]) == true <==> x == y) =
  lemma_operator i f [x; y]

let law_ite (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch) (f:func_decl) (s:sort)
            (c:tvalue u sch bool_sort) (x y:tvalue u sch s)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Choice s)
          (ensures i.application f [c; x; y] == (if truth sch c then x else y)) =
  lemma_operator i f [c; x; y]

(* --- Numerals (op_num_rational [n; d], d > 0; Int numerals have d = 1) -- *)

let law_int_numeral (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch) (f:func_decl)
                    (n:int) (d:pos) (xs:targuments u sch f.domain)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Numeral int_s n d)
          (ensures d == 1 /\ int_of sch (i.application f xs) == n) =
  lemma_operator i f xs

let law_real_numeral (#u:uninterpreted) (#sch:supported_schema) (i:interp u sch) (f:func_decl)
                     (n:int) (d:pos) (xs:targuments u sch f.domain)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Numeral real_s n d)
          (ensures real_of sch (i.application f xs) == of_int n /. of_int d) =
  lemma_operator i f xs

(* --- Integer arithmetic ------------------------------------------------- *)

let law_int_add (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch) (f:func_decl)
                (x y:tvalue u sch int_s)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Arith int_s A.Add /\
                    f.domain == [int_s; int_s])
          (ensures int_of sch (i.application f [x; y]) == int_of sch x + int_of sch y) =
  lemma_operator i f [x; y]

let law_int_mul (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch) (f:func_decl)
                (x y:tvalue u sch int_s)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Arith int_s A.Mul /\
                    f.domain == [int_s; int_s])
          (ensures int_of sch (i.application f [x; y]) == int_of sch x * int_of sch y) =
  lemma_operator i f [x; y]

let law_int_sub (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch) (f:func_decl)
                (x y:tvalue u sch int_s)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Arith int_s A.Sub /\
                    f.domain == [int_s; int_s])
          (ensures int_of sch (i.application f [x; y]) == int_of sch x - int_of sch y) =
  lemma_operator i f [x; y]

let law_int_negate (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch) (f:func_decl)
                   (x:tvalue u sch int_s)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Arith int_s A.Sub /\
                    f.domain == [int_s])
          (ensures int_of sch (i.application f [x]) == - (int_of sch x)) =
  lemma_operator i f [x]

(* n-ary: sum, product, x1 - (x2 + ... + xn) *)
let law_int_nary (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch) (f:func_decl)
                 (o:A.operation) (xs:targuments u sch f.domain)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Arith int_s o)
          (ensures int_of sch (i.application f xs) ==
                   (match o with
                    | A.Add -> isum (ints sch f.domain xs)
                    | A.Mul -> iproduct (ints sch f.domain xs)
                    | _ -> isubtract (ints sch f.domain xs))) =
  lemma_operator i f xs

(* --- Real arithmetic, division, conversion ------------------------------ *)

let law_real_add (#u:uninterpreted) (#sch:supported_schema) (i:interp u sch) (f:func_decl)
                 (x y:tvalue u sch real_s)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Arith real_s A.Add /\
                    f.domain == [real_s; real_s])
          (ensures real_of sch (i.application f [x; y]) == real_of sch x +. real_of sch y) =
  lemma_operator i f [x; y]

let law_real_mul (#u:uninterpreted) (#sch:supported_schema) (i:interp u sch) (f:func_decl)
                 (x y:tvalue u sch real_s)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Arith real_s A.Mul /\
                    f.domain == [real_s; real_s])
          (ensures real_of sch (i.application f [x; y]) == real_of sch x *. real_of sch y) =
  lemma_operator i f [x; y]

let law_real_sub (#u:uninterpreted) (#sch:supported_schema) (i:interp u sch) (f:func_decl)
                 (x y:tvalue u sch real_s)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Arith real_s A.Sub /\
                    f.domain == [real_s; real_s])
          (ensures real_of sch (i.application f [x; y]) == real_of sch x -. real_of sch y) =
  lemma_operator i f [x; y]

let law_real_negate (#u:uninterpreted) (#sch:supported_schema) (i:interp u sch) (f:func_decl)
                    (x:tvalue u sch real_s)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Arith real_s A.Sub /\
                    f.domain == [real_s])
          (ensures real_of sch (i.application f [x]) == 0.0R -. real_of sch x) =
  lemma_operator i f [x]

let law_real_nary (#u:uninterpreted) (#sch:supported_schema) (i:interp u sch) (f:func_decl)
                  (o:A.operation) (xs:targuments u sch f.domain)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Arith real_s o)
          (ensures real_of sch (i.application f xs) ==
                   (match o with
                    | A.Add -> rsum (reals sch f.domain xs)
                    | A.Mul -> rproduct (reals sch f.domain xs)
                    | _ -> rsubtract (reals sch f.domain xs))) =
  lemma_operator i f xs

(* Division by a NONZERO divisor only. x/0 has no law: it stays a free,
   argument-dependent model choice. *)
let law_real_divide (#u:uninterpreted) (#sch:supported_schema) (i:interp u sch) (f:func_decl)
                    (x y:tvalue u sch real_s)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Divide /\
                    ~(real_of sch y == 0.0R))
          (ensures real_of sch (i.application f [x; y]) == real_of sch x /. real_of sch y) =
  lemma_operator i f [x; y]

let law_to_real (#u:uninterpreted) (#sch:supported_schema) (i:interp u sch) (f:func_decl)
                (x:tvalue u sch int_s)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == ToReal)
          (ensures real_of sch (i.application f [x]) == of_int (int_of sch x)) =
  lemma_operator i f [x]

(* --- Comparisons --------------------------------------------------------- *)

let law_int_le (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch) (f:func_decl)
               (x y:tvalue u sch int_s)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Compare int_s A.Le)
          (ensures truth sch (i.application f [x; y]) == (int_of sch x <= int_of sch y)) =
  lemma_operator i f [x; y]

let law_int_lt (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch) (f:func_decl)
               (x y:tvalue u sch int_s)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Compare int_s A.Lt)
          (ensures truth sch (i.application f [x; y]) == (int_of sch x < int_of sch y)) =
  lemma_operator i f [x; y]

let law_int_ge (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch) (f:func_decl)
               (x y:tvalue u sch int_s)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Compare int_s A.Ge)
          (ensures truth sch (i.application f [x; y]) == (int_of sch x >= int_of sch y)) =
  lemma_operator i f [x; y]

let law_int_gt (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch) (f:func_decl)
               (x y:tvalue u sch int_s)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Compare int_s A.Gt)
          (ensures truth sch (i.application f [x; y]) == (int_of sch x > int_of sch y)) =
  lemma_operator i f [x; y]

let law_real_le (#u:uninterpreted) (#sch:supported_schema) (i:interp u sch) (f:func_decl)
                (x y:tvalue u sch real_s)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Compare real_s A.Le)
          (ensures truth sch (i.application f [x; y]) == true <==> real_of sch x <=. real_of sch y) =
  lemma_operator i f [x; y]

let law_real_lt (#u:uninterpreted) (#sch:supported_schema) (i:interp u sch) (f:func_decl)
                (x y:tvalue u sch real_s)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Compare real_s A.Lt)
          (ensures truth sch (i.application f [x; y]) == true <==> real_of sch x <. real_of sch y) =
  lemma_operator i f [x; y]

let law_real_ge (#u:uninterpreted) (#sch:supported_schema) (i:interp u sch) (f:func_decl)
                (x y:tvalue u sch real_s)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Compare real_s A.Ge)
          (ensures truth sch (i.application f [x; y]) == true <==> real_of sch x >=. real_of sch y) =
  lemma_operator i f [x; y]

let law_real_gt (#u:uninterpreted) (#sch:supported_schema) (i:interp u sch) (f:func_decl)
                (x y:tvalue u sch real_s)
  : Lemma (requires root_model u sch i /\ classify (S.signature sch) f == Compare real_s A.Gt)
          (ensures truth sch (i.application f [x; y]) == true <==> real_of sch x >. real_of sch y) =
  lemma_operator i f [x; y]

(* --- Arrays of any arity at supported (datatype-free) sorts ------------- *)
(* The laws are stated for every index list ds, including ds = [] (carrier:
   functions from unit): a root model also exists for that non-SMT sort, but
   it is NOT an SMT-LIB sort and supported_sort (smt_shaped) rejects it at
   any depth, so no coverage claim is made for it. *)

let lemma_classify_select (sigma:V.signature) (ds:list sort) (r:sort)
  : Lemma (requires free sigma (ArraySort ds r))
          (ensures classify sigma (select_decl ds r) == Select ds r) = ()

let lemma_classify_store (sigma:V.signature) (ds:list sort) (r:sort)
  : Lemma (requires free sigma (ArraySort ds r))
          (ensures classify sigma (store_decl ds r) == Store ds r) = ()

(* The argument list of store(a, i1..in, v). *)
let store_arguments (#u:uninterpreted) (#sch:S.checked_schema) (ds:list sort) (r:sort)
                    (a:tvalue u sch (ArraySort ds r)) (ix:targuments u sch ds) (v:tvalue u sch r)
  : targuments u sch (store_decl ds r).domain =
  a :: append_arguments (S.signature sch) ds [r] ix [v]

let rec lemma_split_store (#u:uninterpreted) (#sigma:V.signature)
                          (ds:list sort{not (V.contains_datatype_args sigma ds)})
                          (r:sort{not (V.datatype_sort sigma r)})
                          (ix:V.arguments (carrier u) sigma ds) (v:V.value (carrier u) sigma r)
  : Lemma (ensures split_store #u #sigma ds r (append_arguments sigma ds [r] ix [v]) ==
                   (to_indices #u #sigma ds ix, scalar #u #sigma r v)) (decreases ds) =
  match ds, ix with
  | [], [] -> ()
  | d :: rest, x :: tail -> lemma_split_store #u #sigma rest r tail v
  | _, _ -> ()

let lemma_store_value (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch) (ds:list sort) (r:sort)
                      (a:tvalue u sch (ArraySort ds r)) (ix:targuments u sch ds) (v:tvalue u sch r)
  : Lemma (requires root_model u sch i /\ free (S.signature sch) (ArraySort ds r))
          (ensures i.application (store_decl ds r) (store_arguments ds r a ix v) ==
                   make #u #(S.signature sch) (ArraySort ds r)
                     (write #(indices u ds) #(carrier u r) (scalar #u #(S.signature sch) (ArraySort ds r) a)
                       (to_indices #u #(S.signature sch) ds ix) (scalar #u #(S.signature sch) r v))) =
  lemma_classify_store (S.signature sch) ds r;
  lemma_operator i (store_decl ds r) (store_arguments ds r a ix v);
  lemma_split_store #u #(S.signature sch) ds r ix v

let lemma_select_value (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch) (ds:list sort) (r:sort)
                       (a:tvalue u sch (ArraySort ds r)) (ix:targuments u sch ds)
  : Lemma (requires root_model u sch i /\ free (S.signature sch) (ArraySort ds r))
          (ensures i.application (select_decl ds r) (a :: ix) ==
                   make #u #(S.signature sch) r
                     (read #(indices u ds) #(carrier u r) (scalar #u #(S.signature sch) (ArraySort ds r) a)
                       (to_indices #u #(S.signature sch) ds ix))) =
  lemma_classify_select (S.signature sch) ds r;
  lemma_operator i (select_decl ds r) (a :: ix)

(* select(store(a, i, v), i) = v, every arity *)
let law_select_store_same (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch) (ds:list sort) (r:sort)
                          (a:tvalue u sch (ArraySort ds r)) (ix:targuments u sch ds) (v:tvalue u sch r)
  : Lemma (requires root_model u sch i /\ free (S.signature sch) (ArraySort ds r))
          (ensures i.application (select_decl ds r)
                     (i.application (store_decl ds r) (store_arguments ds r a ix v) :: ix) == v) =
  let sigma = S.signature sch in
  lemma_store_value i ds r a ix v;
  lemma_select_value i ds r (i.application (store_decl ds r) (store_arguments ds r a ix v)) ix;
  lemma_make_scalar #u #sigma r v

(* i <> j (as typed index tuples)  ==>  select(store(a, i, v), j) = select(a, j), every arity *)
let law_select_store_other (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch) (ds:list sort) (r:sort)
                           (a:tvalue u sch (ArraySort ds r)) (ix jx:targuments u sch ds) (v:tvalue u sch r)
  : Lemma (requires root_model u sch i /\ free (S.signature sch) (ArraySort ds r) /\ ~(ix == jx))
          (ensures i.application (select_decl ds r)
                     (i.application (store_decl ds r) (store_arguments ds r a ix v) :: jx) ==
                   i.application (select_decl ds r) (a :: jx)) =
  let sigma = S.signature sch in
  lemma_store_value i ds r a ix v;
  lemma_select_value i ds r (i.application (store_decl ds r) (store_arguments ds r a ix v)) jx;
  lemma_select_value i ds r a jx;
  lemma_from_to #u #sigma ds ix;
  lemma_from_to #u #sigma ds jx

(* Extensionality: arrays that agree on every typed index tuple are equal. *)
let law_array_extensionality (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch) (ds:list sort) (r:sort)
                             (a b:tvalue u sch (ArraySort ds r))
  : Lemma (requires root_model u sch i /\ free (S.signature sch) (ArraySort ds r) /\
                    (forall (jx:targuments u sch ds).
                       i.application (select_decl ds r) (a :: jx) == i.application (select_decl ds r) (b :: jx)))
          (ensures a == b) =
  let sigma = S.signature sch in
  let pointwise (ix:indices u ds)
    : Lemma (read #(indices u ds) #(carrier u r) (scalar #u #sigma (ArraySort ds r) a) ix ==
             read #(indices u ds) #(carrier u r) (scalar #u #sigma (ArraySort ds r) b) ix) =
    let jx = from_indices #u #sigma ds ix in
    lemma_to_from #u #sigma ds ix;
    lemma_select_value i ds r a jx;
    lemma_select_value i ds r b jx in
  FStar.Classical.forall_intro pointwise;
  lemma_array_extensionality #u #sigma ds r a b

(* beta: select(lambda bound. body, i1..in) = body at the REVERSED typed
   arguments (the body sees the innermost binder, the last index, as Var 0). *)
let law_select_lambda (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch) (bound:list sort) (t:sort)
                      (body:body_of u sch bound t) (ix:targuments u sch bound)
  : Lemma (requires root_model u sch i /\ free (S.signature sch) (ArraySort bound t))
          (ensures i.application (select_decl bound t) (i.quantification Lambda_k bound t body :: ix) ==
                   body (reverse_arguments (S.signature sch) bound ix)) =
  let sigma = S.signature sch in
  lemma_select_value i bound t (i.quantification Lambda_k bound t body) ix;
  lemma_from_to #u #sigma bound ix;
  lemma_make_scalar #u #sigma t (body (reverse_arguments sigma bound ix))

(* --- The free choices of the STANDARD family (by design not root laws) --- *)

(* x/0 is uf.apply at the division symbol, a function of both arguments. *)
let lemma_standard_divide_by_zero (u:uninterpreted) (sch:supported_schema) (uf:symbols u sch) (f:func_decl)
                                  (x y:tvalue u sch real_s)
  : Lemma (requires classify (S.signature sch) f == Divide /\ real_of sch y == 0.0R)
          (ensures (standard u sch uf).application f [x; y] == uf.apply f [x; y]) =
  lemma_classified_theory sch f;
  lemma_standard_application u sch uf f [x; y]

(* --- Datatypes: constructor identity and matched fields ----------------- *)

(* A recognizer applied to a constructor tree is true exactly for its own
   constructor (and false for every other constructor of the sort). *)
let law_recognizer (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch)
                   (f:func_decl{Some? (S.find_recognizer f sch.cases)})
                   (d:S.registered_case sch{d.constructor.range ==
                                            (Some?.v (S.find_recognizer f sch.cases)).constructor.range})
                   (ys:targuments u sch d.constructor.domain)
  : Lemma (requires root_model u sch i)
          (ensures truth sch (i.application f [S.constructor_value sch d ys]) ==
                   (d.constructor = (Some?.v (S.find_recognizer f sch.cases)).constructor)) =
  let c = Some?.v (S.find_recognizer f sch.cases) in
  assert (recognizer_at u sch i f);
  assert (recognizer_case u sch i f c (S.constructor_value sch d ys))

(* A matched selector applied to its constructor returns the exact field. *)
let law_accessor (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch)
                 (f:func_decl{Some? (S.find_accessor f sch.cases)})
                 (ys:targuments u sch (Some?.v (S.find_accessor f sch.cases)).matched_case.constructor.domain)
  : Lemma (requires root_model u sch i)
          (ensures i.application f [S.constructor_value sch (Some?.v (S.find_accessor f sch.cases)).matched_case ys] ==
                   field_of #u #sch (Some?.v (S.find_accessor f sch.cases)).matched_case.constructor.domain ys
                     (Some?.v (S.find_accessor f sch.cases)).field) =
  let r = Some?.v (S.find_accessor f sch.cases) in
  assert (accessor_at u sch i f);
  assert (accessor_case u sch i f r ys)

(* ---------------------------------------------------------------------- *)
(* Evaluation of production AST under ANY root model: the evaluator layer  *)
(* ---------------------------------------------------------------------- *)

(* Registered constructors are built by the evaluator (consistent with R4). *)
let lemma_eval_constructor (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch)
                           (scope:list sort) (rho:V.environment (carrier u) (S.signature sch) scope)
                           (f:func_decl) (args:list expr)
  : Lemma (requires D.scoped scope (App f args) /\ L.mem f (S.signature sch))
          (ensures V.evaluate (S.signature sch) i scope rho (App f args) ==
                   V.construct (S.signature sch) f (V.evaluate_args (S.signature sch) i scope rho args f.domain)) = ()

(* Every other application is the interpretation's application. *)
let lemma_eval_application (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch)
                           (scope:list sort) (rho:V.environment (carrier u) (S.signature sch) scope)
                           (f:func_decl) (args:list expr)
  : Lemma (requires D.scoped scope (App f args) /\ not (L.mem f (S.signature sch)))
          (ensures V.evaluate (S.signature sch) i scope rho (App f args) ==
                   i.application f (V.evaluate_args (S.signature sch) i scope rho args f.domain)) = ()

(* Classified theory operators, recognizers and accessors are never
   registered constructors. *)
let lemma_not_registered (sch:S.checked_schema) (f:func_decl)
  : Lemma (requires ~(Other? (classify (S.signature sch) f)) \/ Some? (S.find_recognizer f sch.cases) \/
                    Some? (S.find_accessor f sch.cases))
          (ensures not (L.mem f (S.signature sch))) =
  if L.mem f (S.signature sch) then begin
    lemma_constructor_interp sch f;
    if Some? (S.find_recognizer f sch.cases) then lemma_recognizer_interp f sch.cases;
    if Some? (S.find_accessor f sch.cases) then lemma_accessor_interp f sch.cases;
    if not (Other? (classify (S.signature sch) f)) then lemma_classified_theory sch f
  end

(* R1 at production quantifier nodes, for any root model. *)
let lemma_eval_forall (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch)
                      (scope:list sort) (rho:V.environment (carrier u) (S.signature sch) scope)
                      (bound:list sort) (body:expr)
  : Lemma (requires root_model u sch i /\ D.scoped scope (Quantifier Forall_k bound bool_sort body))
          (ensures truth sch (V.evaluate (S.signature sch) i scope rho
                               (Quantifier Forall_k bound bool_sort body)) == true <==>
                   (forall (vs:targuments u sch (L.rev bound)).
                      truth sch (V.evaluate (S.signature sch) i (L.rev bound @ scope)
                                   (V.extend (S.signature sch) scope (L.rev bound) vs rho) body) == true)) =
  let sigma = S.signature sch in
  let fbody = V.typed_body sigma bound bool_sort (V.evaluate_body sigma i scope rho bound body) in
  assert (forall_case u sch i bound fbody)

let lemma_eval_exists (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch)
                      (scope:list sort) (rho:V.environment (carrier u) (S.signature sch) scope)
                      (bound:list sort) (body:expr)
  : Lemma (requires root_model u sch i /\ D.scoped scope (Quantifier Exists_k bound bool_sort body))
          (ensures truth sch (V.evaluate (S.signature sch) i scope rho
                               (Quantifier Exists_k bound bool_sort body)) == true <==>
                   (exists (vs:targuments u sch (L.rev bound)).
                      truth sch (V.evaluate (S.signature sch) i (L.rev bound @ scope)
                                   (V.extend (S.signature sch) scope (L.rev bound) vs rho) body) == true)) =
  let sigma = S.signature sch in
  let fbody = V.typed_body sigma bound bool_sort (V.evaluate_body sigma i scope rho bound body) in
  assert (exists_case u sch i bound fbody)

(* select of a production lambda node, for any root model and any arity:
   the body is evaluated under the REVERSED typed index arguments. *)
let lemma_eval_select_lambda (#u:uninterpreted) (#sch:S.checked_schema) (i:interp u sch)
                             (scope:list sort) (rho:V.environment (carrier u) (S.signature sch) scope)
                             (bound:list sort) (t:sort) (body:expr) (ix:targuments u sch bound)
  : Lemma (requires root_model u sch i /\ free (S.signature sch) (ArraySort bound t) /\
                    D.scoped scope (Quantifier Lambda_k bound (ArraySort bound t) body) /\ get_sort body == t)
          (ensures i.application (select_decl bound t)
                     (V.evaluate (S.signature sch) i scope rho (Quantifier Lambda_k bound (ArraySort bound t) body) :: ix) ==
                   V.evaluate (S.signature sch) i (L.rev bound @ scope)
                     (V.extend (S.signature sch) scope (L.rev bound)
                       (reverse_arguments (S.signature sch) bound ix) rho) body) =
  let sigma = S.signature sch in
  let fbody = V.typed_body sigma bound t (V.evaluate_body sigma i scope rho bound body) in
  law_select_lambda i bound t fbody ix

(* ---------------------------------------------------------------------- *)
(* The support predicates imply the law preconditions                      *)
(* ---------------------------------------------------------------------- *)

let rec lemma_base_owned (sigma:V.signature) (ds:list sort) (r:sort)
  : Lemma (requires base_owned sigma) (ensures not (V.datatype_sort sigma (ArraySort ds r))) (decreases sigma) =
  match sigma with [] -> () | _ :: rest -> lemma_base_owned rest ds r

(* Bool, Int and Real are the theory sorts of a supported schema. *)
let lemma_supported_primitives (sch:supported_schema)
  : Lemma (not (V.datatype_sort (S.signature sch) bool_sort) /\ not (V.datatype_sort (S.signature sch) int_s) /\
           not (V.datatype_sort (S.signature sch) real_s)) = ()

(* A supported array sort is SMT-shaped (at least one index) and
   datatype-free: select/store are the theory operators and the lambda and
   extensionality laws apply. *)
let lemma_supported_array (sch:supported_schema) (ds:list sort) (r:sort)
  : Lemma (requires supported_sort (S.signature sch) (ArraySort ds r))
          (ensures Cons? ds /\ smt_shaped_all ds /\ smt_shaped r /\ free (S.signature sch) (ArraySort ds r) /\
                   classify (S.signature sch) (select_decl ds r) == Select ds r /\
                   classify (S.signature sch) (store_decl ds r) == Store ds r) =
  lemma_base_owned (S.signature sch) ds r

(* A supported lambda node has a datatype-free array sort. *)
let lemma_supported_lambda (sch:supported_schema) (scope:list sort) (bound:list sort) (s:sort) (body:expr)
  : Lemma (requires supported_expression (S.signature sch) (Quantifier Lambda_k bound s body) /\
                    D.scoped scope (Quantifier Lambda_k bound s body))
          (ensures s == ArraySort bound (get_sort body) /\ free (S.signature sch) (ArraySort bound (get_sort body))) =
  lemma_base_owned (S.signature sch) bound (get_sort body)

(* Every binder of a supported quantifier is a supported sort. *)
let lemma_supported_binders (sigma:V.signature) (k:quantifier_kind) (bound:list sort) (s:sort) (body:expr)
  : Lemma (requires supported_expression sigma (Quantifier k bound s body))
          (ensures supported_sorts sigma bound /\ supported_expression sigma body) = ()

(* Every declaration of a supported application has supported domain and range. *)
let lemma_supported_application (sigma:V.signature) (f:func_decl) (args:list expr)
  : Lemma (requires supported_expression sigma (App f args))
          (ensures supported_sort sigma f.range /\ supported_sorts sigma f.domain /\
                   supported_expressions sigma args) = ()

(* --- Document-level support induction ---------------------------------- *)

(* x occurs in e: the reflexive subterm relation of the production AST
   (every argument of an application, the body of every quantifier and
   lambda, at every depth). *)
let rec occurs (x e:expr) : Tot bool (decreases e) =
  x = e ||
  (match e with
   | Var _ _ -> false
   | App _ args -> occurs_in x args
   | Quantifier _ _ _ body -> occurs x body)

and occurs_in (x:expr) (es:list expr) : Tot bool (decreases es) =
  match es with [] -> false | e :: rest -> occurs x e || occurs_in x rest

(* Support is inherited by every subterm. *)
let rec lemma_supported_occurs (sigma:V.signature) (x e:expr)
  : Lemma (requires supported_expression sigma e /\ occurs x e)
          (ensures supported_expression sigma x) (decreases e) =
  if x = e then ()
  else match e with
  | Var _ _ -> ()
  | App _ args -> lemma_supported_occurs_in sigma x args
  | Quantifier _ _ _ body -> lemma_supported_occurs sigma x body

and lemma_supported_occurs_in (sigma:V.signature) (x:expr) (es:list expr)
  : Lemma (requires supported_expressions sigma es /\ occurs_in x es)
          (ensures supported_expression sigma x) (decreases es) =
  match es with
  | [] -> ()
  | e :: rest -> if occurs x e then lemma_supported_occurs sigma x e else lemma_supported_occurs_in sigma x rest

(* List membership. *)
let rec lemma_supported_sorts_mem (sigma:V.signature) (ss:list sort) (s:sort)
  : Lemma (requires supported_sorts sigma ss /\ L.mem s ss) (ensures supported_sort sigma s) (decreases ss) =
  match ss with [] -> () | t :: rest -> if t = s then () else lemma_supported_sorts_mem sigma rest s

let rec lemma_supported_expressions_mem (sigma:V.signature) (es:list expr) (e:expr)
  : Lemma (requires supported_expressions sigma es /\ L.mem e es) (ensures supported_expression sigma e)
          (decreases es) =
  match es with [] -> () | d :: rest -> if d = e then () else lemma_supported_expressions_mem sigma rest e

(* What the laws need of a sort occurring in a supported term over a
   supported schema: support, SMT shape, and an array sort is datatype-free
   with at least one index (so select/store classify as the theory
   operators and the array/lambda laws apply, with an SMT meaning). *)
let sort_ready (sigma:V.signature) (s:sort) : prop =
  supported_sort sigma s /\ smt_shaped s /\
  (ArraySort? s ==> free sigma s /\ Cons? (ArraySort?.domain s))

(* Every sort of one node: a variable's sort label, a declaration's range
   and every domain sort, a quantifier/lambda sort and every binder sort. *)
let node_ready (sigma:V.signature) (x:expr) : prop =
  match x with
  | Var _ s -> sort_ready sigma s
  | App f _ -> sort_ready sigma f.range /\ (forall (s:sort). L.mem s f.domain ==> sort_ready sigma s)
  | Quantifier _ bound s _ -> sort_ready sigma s /\ (forall (b:sort). L.mem b bound ==> sort_ready sigma b)

let lemma_sort_ready (sch:supported_schema) (s:sort)
  : Lemma (requires supported_sort (S.signature sch) s) (ensures sort_ready (S.signature sch) s) =
  match s with ArraySort ds r -> lemma_base_owned (S.signature sch) ds r | BaseSort _ -> ()

let rec lemma_sorts_ready (sch:supported_schema) (ss:list sort)
  : Lemma (requires supported_sorts (S.signature sch) ss)
          (ensures forall (s:sort). L.mem s ss ==> sort_ready (S.signature sch) s) (decreases ss) =
  match ss with [] -> () | s :: rest -> lemma_sort_ready sch s; lemma_sorts_ready sch rest

let lemma_node_ready (sch:supported_schema) (x:expr)
  : Lemma (requires supported_expression (S.signature sch) x) (ensures node_ready (S.signature sch) x) =
  match x with
  | Var _ s -> lemma_sort_ready sch s
  | App f _ -> lemma_sort_ready sch f.range; lemma_sorts_ready sch f.domain
  | Quantifier _ bound s _ -> lemma_sort_ready sch s; lemma_sorts_ready sch bound

(* THE document-level lemma: every node occurring in any expression of a
   supported document is supported and law-ready. Coverage only: a future
   L2 must ALSO establish D.scoped (typing) for the same document. *)
let lemma_document_node (sch:S.schema) (es:list expr) (e x:expr)
  : Lemma (requires supported_document sch es /\ L.mem e es /\ occurs x e)
          (ensures supported sch /\ supported_expression (S.signature sch) x /\ node_ready (S.signature sch) x) =
  lemma_supported_expressions_mem (S.signature sch) es e;
  lemma_supported_occurs (S.signature sch) x e;
  lemma_node_ready sch x

(* Every constructor field of a supported schema is law-ready (the values
   quantified over at a datatype sort only contain law-ready scalars). *)
let rec lemma_fields_ready_in (sch:supported_schema) (cs:list S.constructor_case) (c:S.constructor_case)
  : Lemma (requires fields_supported (S.signature sch) cs /\ L.mem c cs)
          (ensures forall (s:sort). L.mem s c.S.constructor.domain ==> sort_ready (S.signature sch) s)
          (decreases cs) =
  match cs with
  | [] -> ()
  | d :: rest ->
    if d = c then lemma_sorts_ready sch c.S.constructor.domain else lemma_fields_ready_in sch rest c

let lemma_fields_ready (sch:supported_schema) (c:S.constructor_case)
  : Lemma (requires L.mem c sch.S.cases)
          (ensures forall (s:sort). L.mem s c.S.constructor.domain ==> sort_ready (S.signature sch) s) =
  lemma_fields_ready_in sch sch.S.cases c

(* Canonical declarations of the interpreted primitive operators. *)
let true_decl : func_decl = { decl_name = "true"; domain = []; range = bool_sort; interp = Some op_true; int_params = [] }
let false_decl : func_decl = { decl_name = "false"; domain = []; range = bool_sort; interp = Some op_false; int_params = [] }
let not_decl : func_decl = { decl_name = "not"; domain = [bool_sort]; range = bool_sort; interp = Some op_not; int_params = [] }
let implies_decl : func_decl =
  { decl_name = "=>"; domain = [bool_sort; bool_sort]; range = bool_sort; interp = Some op_implies; int_params = [] }
let bool2_decl (name:string) (tag:decl_kind) : func_decl =
  { decl_name = name; domain = [bool_sort; bool_sort]; range = bool_sort; interp = Some tag; int_params = [] }
let int_numeral (n:int) : func_decl =
  { decl_name = "num"; domain = []; range = int_s; interp = Some op_num_rational; int_params = [n; 1] }
let real_numeral (n:int) (d:pos) : func_decl =
  { decl_name = "num"; domain = []; range = real_s; interp = Some op_num_rational; int_params = [n; d] }
let binary_decl (s:sort) (name:string) (tag:decl_kind) (range:sort) : func_decl =
  { decl_name = name; domain = [s; s]; range = range; interp = Some tag; int_params = [] }
let negate_decl (s:sort) : func_decl =
  { decl_name = "-"; domain = [s]; range = s; interp = Some op_arith_sub; int_params = [] }
let to_real_decl : func_decl =
  { decl_name = "to_real"; domain = [int_s]; range = real_s; interp = Some op_to_real; int_params = [] }

let lemma_classify_booleans (sigma:V.signature) (s:sort)
  : Lemma (classify sigma true_decl == Constant true /\ classify sigma false_decl == Constant false /\
           classify sigma not_decl == Negation /\ classify sigma implies_decl == Implication /\
           classify sigma (bool2_decl "and" op_and) == Nary B.And /\
           classify sigma (bool2_decl "or" op_or) == Nary B.Or /\
           classify sigma (bool2_decl "xor" op_xor) == Nary B.Xor /\
           classify sigma (R.eq_decl s) == Equality s /\ classify sigma (ite_decl s) == Choice s) = ()

let lemma_classify_numerals (sch:supported_schema) (n:int) (d:pos)
  : Lemma (classify (S.signature sch) (int_numeral n) == Numeral int_s n 1 /\
           classify (S.signature sch) (real_numeral n d) == Numeral real_s n d) = ()

let plus_decl (s:sort) : func_decl = binary_decl s "+" op_arith_add s
let times_decl (s:sort) : func_decl = binary_decl s "*" op_arith_mul s
let minus_decl (s:sort) : func_decl = binary_decl s "-" op_arith_sub s
let divide_decl : func_decl = binary_decl real_s "/" op_arith_div real_s
let le_decl (s:sort) : func_decl = binary_decl s "<=" op_arith_le bool_sort
let lt_decl (s:sort) : func_decl = binary_decl s "<" op_arith_lt bool_sort
let ge_decl (s:sort) : func_decl = binary_decl s ">=" op_arith_ge bool_sort
let gt_decl (s:sort) : func_decl = binary_decl s ">" op_arith_gt bool_sort

type numeric_sort = s:sort{s == int_s \/ s == real_s}

(* One small lemma per operator (a single conjunction took 6-9 s). *)
let lemma_classify_plus (sch:supported_schema) (s:numeric_sort)
  : Lemma (classify (S.signature sch) (plus_decl s) == Arith s A.Add) = ()
let lemma_classify_times (sch:supported_schema) (s:numeric_sort)
  : Lemma (classify (S.signature sch) (times_decl s) == Arith s A.Mul) = ()
let lemma_classify_minus (sch:supported_schema) (s:numeric_sort)
  : Lemma (classify (S.signature sch) (minus_decl s) == Arith s A.Sub) = ()
let lemma_classify_negate (sch:supported_schema) (s:numeric_sort)
  : Lemma (classify (S.signature sch) (negate_decl s) == Arith s A.Sub) = ()
let lemma_classify_le (sch:supported_schema) (s:numeric_sort)
  : Lemma (classify (S.signature sch) (le_decl s) == Compare s A.Le) = ()
let lemma_classify_lt (sch:supported_schema) (s:numeric_sort)
  : Lemma (classify (S.signature sch) (lt_decl s) == Compare s A.Lt) = ()
let lemma_classify_ge (sch:supported_schema) (s:numeric_sort)
  : Lemma (classify (S.signature sch) (ge_decl s) == Compare s A.Ge) = ()
let lemma_classify_gt (sch:supported_schema) (s:numeric_sort)
  : Lemma (classify (S.signature sch) (gt_decl s) == Compare s A.Gt) = ()
let lemma_classify_divide (sch:supported_schema)
  : Lemma (classify (S.signature sch) divide_decl == Divide) = ()
let lemma_classify_to_real (sch:supported_schema)
  : Lemma (classify (S.signature sch) to_real_decl == ToReal) = ()

(* Native records. Z3NativeProof.operator_tag gives binary Int + and * the
   tags op_plus/op_mul (every other arity, and every Real +/*, gets
   op_arith_add/op_arith_mul, covered by plus_decl/times_decl above and the
   n-ary laws); the native exporter gives them the Z3 names "+"/"*" and no
   parameters (Z3Native.view_expression). Name, tag, sorts and parameters
   are all checked: any mismatch classifies Other (pinned in the tests). *)
let native_plus_int : func_decl = binary_decl int_s "+" op_plus int_s
let native_times_int : func_decl = binary_decl int_s "*" op_mul int_s

let lemma_classify_native_plus (sch:S.checked_schema)
  : Lemma (classify (S.signature sch) native_plus_int == Arith int_s A.Add) = ()
let lemma_classify_native_times (sch:S.checked_schema)
  : Lemma (classify (S.signature sch) native_times_int == Arith int_s A.Mul) = ()

(* Nullary policy: canonical nullary + and * are the empty sum and the
   empty product (law_int_nary/law_real_nary then give 0 and 1); nullary -
   stays free. See `numeric`. *)
let nullary_decl (s:sort) (name:string) (tag:decl_kind) : func_decl =
  { decl_name = name; domain = []; range = s; interp = Some tag; int_params = [] }
let empty_sum_decl (s:sort) : func_decl = nullary_decl s "+" op_arith_add
let empty_product_decl (s:sort) : func_decl = nullary_decl s "*" op_arith_mul

let lemma_classify_empty_sum (sch:supported_schema) (s:numeric_sort)
  : Lemma (classify (S.signature sch) (empty_sum_decl s) == Arith s A.Add) = ()
let lemma_classify_empty_product (sch:supported_schema) (s:numeric_sort)
  : Lemma (classify (S.signature sch) (empty_product_decl s) == Arith s A.Mul) = ()
let lemma_classify_nullary_minus (sch:supported_schema) (s:numeric_sort)
  : Lemma (classify (S.signature sch) (nullary_decl s "-" op_arith_sub) == Other) = ()
