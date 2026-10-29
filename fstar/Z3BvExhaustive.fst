module Z3BvExhaustive

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
module D = Z3Definitions
module L = FStar.List.Tot
module U = FStar.UInt
module BV = Z3BvLemma
module C = Z3CanonicalOps
module SM = Z3StandardModel

(* Bounded exhaustive evaluation of bit-vector clauses over opaque leaves.

   A premise-free `th-lemma` or `rewrite` step over bit-vectors is decided by
   evaluating it under every assignment of values to its leaves. The evaluated
   fragment is small: Boolean `true`, `false`, `not`, `and`, `or`, `=` on
   Booleans and on bit-vectors, the unsigned comparisons `bvult`/`bvule`/
   `bvuge`, bit-vector numerals, `concat` of two arguments, `extract`,
   `zero_extend`, and `bvadd` of two arguments. The connectives are
   recognized by the typed canonical predicates of `Z3CanonicalOps` (name,
   kind tag, domain, range and parameters), never by their name alone. The
   bit-vector operators are recognized by the `Z3BvLemma` recognizers, which
   check the declaration's parameters, domain, range and argument sorts. Each
   is evaluated exactly as the matching contract of
   `Z3StandardModel.ground_model` describes it. A declaration named `=` or
   `and` whose kind tag is a bit-vector or datatype kind is therefore never
   evaluated as a connective.

   Soundness is proved from `Z3StandardModel.ground_model`, the ground
   Boolean and bit-vector contracts (`lemma_valid_ground`). Every standard
   interpretation `Z3StandardModel.standard leaf` satisfies them, so that
   theorem has models, and an accepted clause is true in each of them
   (`lemma_valid_standard`). The kernel's hypotheses imply `ground_model`
   (`Z3StandardModel.lemma_ground_of_global`), but the kernel's theorem is
   still stated over `Z3UnifiedProof.model_sound`, which has no model, so the
   kernel-level statement remains vacuous until the global contracts are
   repaired.

   A leaf is a closed bit-vector term of a known width `w` whose head is not
   one of those operators, such as `(select a i)`, an uninterpreted constant,
   or a bit-vector operator outside the fragment such as `bvmul`. A leaf is
   never evaluated: structurally equal leaves of the same width share one
   value, distinct leaves are enumerated independently over every value in
   [0, 2^w). Under `ground_model` the value of any closed ground term of sort
   `BV<w>` lies in that range, so a clause that evaluates to true under every
   enumerated assignment holds in every model. A term whose declaration claims
   one of the evaluated bit-vector kinds but is malformed (wrong parameters,
   widths, arity or sorts, or a numeral out of range) is neither evaluated nor
   treated as a leaf; the clause stays unchecked. Boolean terms outside the
   fragment, such as the signed comparisons and `bit2bool` that the native
   bridge leaves opaque, are never leaves either.

   Bounds, all tested before anything is enumerated: the expression has at
   most `max_nodes` occurrences (counted on the tree, so a shared DAG cannot
   hide its size), contains no variable or binder, and its leaves have at
   most `max_leaf_bits` bits in total, hence at most 2^12 = 4096 assignments.
   Anything outside the fragment or the bounds leaves the step pending; it is
   never rejected. *)

let max_leaf_bits : nat = 12
let max_nodes : nat = 512

type leaf_table = list (expr & pos)

let rec index_of (x:expr & pos) (tbl:leaf_table) : Tot (option nat) (decreases tbl) =
  match tbl with
  | [] -> None
  | y :: rest ->
    if y = x then Some 0
    else (match index_of x rest with Some k -> Some (k + 1) | None -> None)

(* Declarations of the evaluated bit-vector kinds: one that fails its
   recognizer is malformed and is not an opaque leaf. *)
let reserved (f:func_decl) : bool =
  f.interp = Some BV.op_numeral || f.interp = Some BV.op_extract ||
  f.interp = Some BV.op_concat || f.interp = Some BV.op_zero_extend ||
  f.interp = Some BV.op_add

let leaf (tbl:leaf_table) (v:nat -> int) (w:pos) (e:expr) : option int =
  match e with
  | App f _ ->
    if get_sort e = BV.bv_sort w && not (reserved f)
    then (match index_of (e, w) tbl with Some k -> Some (v k) | None -> None)
    else None
  | _ -> None

(* The value of a term of sort `BV<w>` when the k-th leaf of `tbl` has value
   `v k`; `None` outside the fragment or at a width mismatch. *)
let rec eval_bv (tbl:leaf_table) (v:nat -> int) (w:pos) (e:expr) : Tot (option int) (decreases e) =
  match BV.numeral e with
  | Some (q, n) -> if q = w then Some n else None
  | None ->
    (match e with
     | App f [x] ->
       (match BV.extract_parts e, BV.zero_extend_parts e with
        | Some s, _ ->
          if s.BV.high - s.BV.low + 1 = w then
            (match eval_bv tbl v s.BV.source_width x with
             | Some a -> Some ((a / pow2 s.BV.low) % pow2 w)
             | None -> None)
          else None
        | None, Some z ->
          if z.BV.input_width + z.BV.extra_width = w then eval_bv tbl v z.BV.input_width x else None
        | None, None -> leaf tbl v w e)
     | App f [x; y] ->
       (match BV.concat_parts e, BV.operation f [x; y] with
        | Some c, _ ->
          if c.BV.left_width + c.BV.right_width = w then
            (match eval_bv tbl v c.BV.left_width x, eval_bv tbl v c.BV.right_width y with
             | Some a, Some b -> Some (a * pow2 c.BV.right_width + b)
             | _, _ -> None)
          else None
        | None, Some (q, op) ->
          if q = w && op = BV.op_add then
            (match eval_bv tbl v w x, eval_bv tbl v w y with
             | Some a, Some b -> Some ((a + b) % pow2 w)
             | _, _ -> None)
          else leaf tbl v w e
        | None, None -> leaf tbl v w e)
     | _ -> leaf tbl v w e)

(* The width of an evaluated bit-vector operator application. *)
let bv_width (e:expr) : option pos =
  match BV.numeral e with
  | Some (w, _) -> Some w
  | None ->
    (match BV.extract_parts e, BV.zero_extend_parts e, BV.concat_parts e with
     | Some s, _, _ -> Some (s.BV.high - s.BV.low + 1)
     | _, Some z, _ -> Some (z.BV.input_width + z.BV.extra_width)
     | _, _, Some c -> Some (c.BV.left_width + c.BV.right_width)
     | _, _, _ ->
       (match e with
        | App f [x; y] ->
          (match BV.operation f [x; y] with
           | Some (w, op) -> if op = BV.op_add then Some w else None
           | None -> None)
        | _ -> None))

let equal_width (a b:expr) : option pos =
  match bv_width a with
  | Some w -> Some w
  | None -> bv_width b

let boolean_pair (a b:expr) : bool = get_sort a = bool_sort && get_sort b = bool_sort

let rec eval_bool (tbl:leaf_table) (v:nat -> int) (e:expr) : Tot (option bool) (decreases e) =
  match e with
  | App f args ->
    if get_sort e <> bool_sort then None
    else if C.canonical_true f && args = [] then Some true
    else if C.canonical_false f && args = [] then Some false
    else if C.canonical_not f then
      (match args with
       | [a] -> (match eval_bool tbl v a with Some b -> Some (not b) | None -> None)
       | _ -> None)
    else if C.canonical_or f then eval_or tbl v args
    else if C.canonical_and f then eval_and tbl v args
    else if C.canonical_eq f then
      (match args with
       | [a; b] ->
         if boolean_pair a b then
           (match eval_bool tbl v a, eval_bool tbl v b with
            | Some x, Some y -> Some (x = y)
            | _, _ -> None)
         else
           (match equal_width a b with
            | Some w ->
              (match eval_bv tbl v w a, eval_bv tbl v w b with
               | Some x, Some y -> Some (x = y)
               | _, _ -> None)
            | None -> None)
       | _ -> None)
    else
      (match args with
       | [a; b] ->
         (match BV.unsigned_parts e with
          | Some c ->
            (match eval_bv tbl v c.BV.width a, eval_bv tbl v c.BV.width b with
             | Some x, Some y -> Some (BV.unsigned_value c.BV.relation x y)
             | _, _ -> None)
          | None -> None)
       | _ -> None)
  | _ -> None

and eval_or (tbl:leaf_table) (v:nat -> int) (args:list expr) : Tot (option bool) (decreases args) =
  match args with
  | [] -> Some false
  | a :: rest ->
    (match eval_bool tbl v a, eval_or tbl v rest with
     | Some x, Some y -> Some (x || y)
     | _, _ -> None)

and eval_and (tbl:leaf_table) (v:nat -> int) (args:list expr) : Tot (option bool) (decreases args) =
  match args with
  | [] -> Some true
  | a :: rest ->
    (match eval_bool tbl v a, eval_and tbl v rest with
     | Some x, Some y -> Some (x && y)
     | _, _ -> None)

(* Untrusted collection of the leaves, following `eval_bv`/`eval_bool`; a
   missing leaf only makes the evaluation fail. Each leaf is recorded once. *)
let add_leaf (tbl:leaf_table) (x:expr & pos) : leaf_table =
  if L.mem x tbl then tbl else L.append tbl [x]

let rec leaves_bv (tbl:leaf_table) (w:pos) (e:expr) : Tot leaf_table (decreases e) =
  match BV.numeral e with
  | Some _ -> tbl
  | None ->
    (match e with
     | App f [x] ->
       (match BV.extract_parts e, BV.zero_extend_parts e with
        | Some s, _ -> leaves_bv tbl s.BV.source_width x
        | None, Some z -> leaves_bv tbl z.BV.input_width x
        | None, None -> add_leaf tbl (e, w))
     | App f [x; y] ->
       (match BV.concat_parts e, BV.operation f [x; y] with
        | Some c, _ -> leaves_bv (leaves_bv tbl c.BV.left_width x) c.BV.right_width y
        | None, Some (q, op) ->
          if op = BV.op_add then leaves_bv (leaves_bv tbl q x) q y else add_leaf tbl (e, w)
        | None, None -> add_leaf tbl (e, w))
     | _ -> add_leaf tbl (e, w))

let rec leaves_bool (tbl:leaf_table) (e:expr) : Tot leaf_table (decreases e) =
  match e with
  | App f args ->
    if C.canonical_not f || C.canonical_or f || C.canonical_and f then leaves_bools tbl args
    else if C.canonical_eq f then
      (match args with
       | [a; b] ->
         if boolean_pair a b then leaves_bool (leaves_bool tbl a) b
         else (match equal_width a b with
               | Some w -> leaves_bv (leaves_bv tbl w a) w b
               | None -> tbl)
       | _ -> tbl)
    else
      (match args with
       | [a; b] ->
         (match BV.unsigned_parts e with
          | Some c -> leaves_bv (leaves_bv tbl c.BV.width a) c.BV.width b
          | None -> tbl)
       | _ -> tbl)
  | _ -> tbl

and leaves_bools (tbl:leaf_table) (args:list expr) : Tot leaf_table (decreases args) =
  match args with
  | [] -> tbl
  | a :: rest -> leaves_bools (leaves_bool tbl a) rest

(* The total width of the leaves, abandoned as soon as it exceeds the bound. *)
let rec within_bits (tbl:leaf_table) (acc:nat) : Tot bool (decreases tbl) =
  if acc > max_leaf_bits then false
  else match tbl with
       | [] -> true
       | (_, w) :: rest -> within_bits rest (acc + w)

(* Every leaf is a closed ground term of its width, at most 4096 bits wide
   (the leaves are subterms of the checked ground clause and their widths add
   up to at most `max_leaf_bits`, so this test never fails on a collected
   table; it states what the soundness proof uses). *)
let closed_leaf (x:expr & pos) : bool =
  SM.closed_ground (fst x) && snd x <= SM.max_width && get_sort (fst x) = BV.bv_sort (snd x)

let rec widths (tbl:leaf_table) : Tot (list pos) (decreases tbl) =
  match tbl with
  | [] -> []
  | (_, w) :: rest -> w :: widths rest

(* `for_all_vectors ws f` evaluates `f` on every list whose k-th entry is in
   [0, 2^(ws_k)). *)
let with_head (f:list int -> bool) (x:int) (r:list int) : bool = f (x :: r)

let rec for_all_vectors (ws:list pos) (f:list int -> bool) : Tot bool (decreases %[ws; 0; 0]) =
  match ws with
  | [] -> f []
  | w :: rest -> for_all_heads rest (pow2 w) f

and for_all_heads (rest:list pos) (k:nat) (f:list int -> bool) : Tot bool (decreases %[rest; 1; k]) =
  if k = 0 then true
  else for_all_vectors rest (with_head f (k - 1)) && for_all_heads rest (k - 1) f

let vector_value (r:list int) : nat -> int =
  fun k -> if k < L.length r then L.index r k else 0

let clause_true (tbl:leaf_table) (e:expr) (r:list int) : bool =
  eval_bool tbl (vector_value r) e = Some true

(* The side conditions are tested in order and each guards the next: the size
   bound before any traversal, closedness, then the leaf-width bound before
   any assignment is enumerated. The guards are conditionals rather than
   conjunctions so that the order also holds under normalization, which
   evaluates both operands of `&&`. *)
let valid (e:expr) : bool =
  if not (Some? (expression_budget max_nodes e)) then false
  else if not (SM.closed_ground e) then false
  else
    let tbl = leaves_bool [] e in
    if not (within_bits tbl 0) then false
    else if not (L.for_all closed_leaf tbl) then false
    else for_all_vectors (widths tbl) (clause_true tbl e)

(* A rewrite `a = b` (or `a ~ b`) holds when the equation is valid. *)
let equivalent (a b:expr) : bool = valid (mk_eq_expr a b)

(* --- The bound ------------------------------------------------------ *)

let rec total_bits (tbl:leaf_table) : Tot nat (decreases tbl) =
  match tbl with
  | [] -> 0
  | (_, w) :: rest -> w + total_bits rest

(* The enumeration is entered only when the leaves have at most 12 bits in
   total, that is at most 2^12 = 4096 assignments. *)
let rec lemma_within_bits (tbl:leaf_table) (acc:nat)
  : Lemma (requires within_bits tbl acc)
          (ensures acc + total_bits tbl <= max_leaf_bits)
          (decreases tbl)
  = match tbl with
    | [] -> ()
    | (_, w) :: rest -> lemma_within_bits rest (acc + w)

(* --- Soundness ------------------------------------------------------ *)

let rec lemma_index_of (x:expr & pos) (tbl:leaf_table) (k:nat)
  : Lemma (requires index_of x tbl == Some k)
          (ensures k < L.length tbl /\ L.index tbl k == x)
          (decreases tbl)
  = match tbl with
    | y :: rest ->
      if y = x then ()
      else (match index_of x rest with
            | Some j -> lemma_index_of x rest j
            | None -> ())

let rec in_range (ws:list pos) (r:list int) : Tot bool (decreases ws) =
  match ws, r with
  | [], [] -> true
  | w :: ws', x :: r' -> 0 <= x && x < pow2 w && in_range ws' r'
  | _, _ -> false

(* Coverage: every vector in range is enumerated. *)
let rec lemma_for_all_vectors (ws:list pos) (f:list int -> bool) (r:list int)
  : Lemma (requires for_all_vectors ws f /\ in_range ws r)
          (ensures f r)
          (decreases %[ws; 0; 0])
  = match ws, r with
    | [], [] -> ()
    | w :: rest, x :: r' -> lemma_for_all_heads rest (pow2 w) f x r'

and lemma_for_all_heads (rest:list pos) (k:nat) (f:list int -> bool) (x:int) (r':list int)
  : Lemma (requires for_all_heads rest k f /\ 0 <= x /\ x < k /\ in_range rest r')
          (ensures f (x :: r'))
          (decreases %[rest; 1; k])
  = if x = k - 1 then lemma_for_all_vectors rest (with_head f (k - 1)) r'
    else lemma_for_all_heads rest (k - 1) f x r'

(* The assignment `v` gives every leaf its value in the model. *)
let agrees (i:interpretation value) (rho:env value) (project:pos -> value -> int)
           (tbl:leaf_table) (v:nat -> int) : prop =
  forall (k:nat). k < L.length tbl ==>
    v k == project (snd (L.index tbl k)) (eval i (fst (L.index tbl k)) rho)

(* The hypotheses of the evaluation: the ground Boolean and bit-vector
   contracts. They have models (`Z3StandardModel.lemma_standard_model`). *)
let eval_model (i:interpretation value) (project:pos -> value -> int) : prop =
  SM.ground_model i project

let lemma_scoped_app (f:func_decl) (args:list expr)
  : Lemma (requires SM.closed_ground (App f args)) (ensures SM.closed_args args)
  = SM.lemma_closed_app f args

let lemma_scoped_cons (a:expr) (rest:list expr)
  : Lemma (requires SM.closed_args (a :: rest)) (ensures SM.closed_ground a /\ SM.closed_args rest)
  = SM.lemma_closed_cons a rest

let lemma_leaf (i:interpretation value) (rho:env value) (project:pos -> value -> int)
               (tbl:leaf_table) (v:nat -> int) (w:pos) (e:expr)
  : Lemma (requires agrees i rho project tbl v /\ Some? (leaf tbl v w e))
          (ensures get_sort e == BV.bv_sort w /\ project w (eval i e rho) == Some?.v (leaf tbl v w e))
  = let k = Some?.v (index_of (e, w) tbl) in
    lemma_index_of (e, w) tbl k

let lemma_add (i:interpretation value) (rho:env value) (project:pos -> value -> int)
              (f:func_decl) (x y:expr) (w:pos)
  : Lemma (requires SM.ground_bv i project /\ SM.closed_ground (App f [x; y]) /\
                    BV.operation f [x; y] == Some (w, BV.op_add) /\
                    SM.closed_ground x /\ SM.closed_ground y /\
                    get_sort x == BV.bv_sort w /\ get_sort y == BV.bv_sort w)
          (ensures get_sort (App f [x; y]) == BV.bv_sort w /\
                   project w (eval i (App f [x; y]) rho) ==
                   (project w (eval i x rho) + project w (eval i y rho)) % pow2 w)
  = SM.lemma_ground_operation i rho project f [x; y] w BV.op_add;
    SM.lemma_ground_word i rho project w x;
    SM.lemma_ground_word i rho project w y;
    assert_norm (eval_args i [x; y] rho == [eval i x rho; eval i y rho]);
    assert_norm (BV.words w project [eval i x rho; eval i y rho] ==
                 [U.to_uint_t w (project w (eval i x rho)); U.to_uint_t w (project w (eval i y rho))])

(* One unfolding of `eval_bv` at a binary `bvadd`, kept out of the recursive lemma below. *)
let lemma_eval_bv_add (tbl:leaf_table) (v:nat -> int) (w:pos) (f:func_decl) (x y:expr)
  : Lemma (requires None? (BV.numeral (App f [x; y])) /\ None? (BV.concat_parts (App f [x; y])) /\
                    BV.operation f [x; y] == Some (w, BV.op_add) /\ Some? (eval_bv tbl v w (App f [x; y])))
          (ensures Some? (eval_bv tbl v w x) /\ Some? (eval_bv tbl v w y) /\
                   Some?.v (eval_bv tbl v w (App f [x; y])) ==
                   (Some?.v (eval_bv tbl v w x) + Some?.v (eval_bv tbl v w y)) % pow2 w)
  = ()

(* The same for a binary `concat`. *)
let lemma_eval_bv_concat (tbl:leaf_table) (v:nat -> int) (w:pos) (f:func_decl) (x y:expr)
                         (c:BV.concatenation)
  : Lemma (requires None? (BV.numeral (App f [x; y])) /\ BV.concat_parts (App f [x; y]) == Some c /\
                    Some? (eval_bv tbl v w (App f [x; y])))
          (ensures c.BV.left == x /\ c.BV.right == y /\ c.BV.left_width + c.BV.right_width == w /\
                   Some? (eval_bv tbl v c.BV.left_width x) /\ Some? (eval_bv tbl v c.BV.right_width y) /\
                   Some?.v (eval_bv tbl v w (App f [x; y])) ==
                   Some?.v (eval_bv tbl v c.BV.left_width x) * pow2 c.BV.right_width +
                   Some?.v (eval_bv tbl v c.BV.right_width y))
  = ()

(* The remaining shapes of `eval_bv` are leaves, also kept out of the recursive lemma. *)
let lemma_eval_bv_other (tbl:leaf_table) (v:nat -> int) (w:pos) (e:expr)
  : Lemma (requires None? (BV.numeral e) /\ (match e with App _ [_] | App _ [_; _] -> False | _ -> True))
          (ensures eval_bv tbl v w e == leaf tbl v w e)
  = ()

(* The value of an `eval_bv` case once its arguments are known to have their values (the induction
   hypothesis of `lemma_eval_bv`); each is stated separately to keep the recursive lemma small. *)
let value_of (i:interpretation value) (rho:env value) (project:pos -> value -> int)
             (tbl:leaf_table) (v:nat -> int) (w:pos) (e:expr) : prop =
  Some? (eval_bv tbl v w e) /\ get_sort e == BV.bv_sort w /\
  project w (eval i e rho) == Some?.v (eval_bv tbl v w e)

let lemma_concat_case (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                      (tbl:leaf_table) (v:nat -> int) (w:pos) (f:func_decl) (x y:expr) (c:BV.concatenation)
  : Lemma (requires SM.ground_bv i project /\ SM.closed_ground (App f [x; y]) /\
                    None? (BV.numeral (App f [x; y])) /\ BV.concat_parts (App f [x; y]) == Some c /\
                    Some? (eval_bv tbl v w (App f [x; y])) /\
                    value_of i rho project tbl v c.BV.left_width x /\
                    value_of i rho project tbl v c.BV.right_width y)
          (ensures value_of i rho project tbl v w (App f [x; y]))
  = lemma_eval_bv_concat tbl v w f x y c;
    SM.lemma_ground_concat i rho project (App f [x; y]) c

let lemma_add_case (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                   (tbl:leaf_table) (v:nat -> int) (w:pos) (f:func_decl) (x y:expr)
  : Lemma (requires SM.ground_bv i project /\ SM.closed_ground (App f [x; y]) /\
                    None? (BV.numeral (App f [x; y])) /\ None? (BV.concat_parts (App f [x; y])) /\
                    BV.operation f [x; y] == Some (w, BV.op_add) /\
                    Some? (eval_bv tbl v w (App f [x; y])) /\
                    value_of i rho project tbl v w x /\ value_of i rho project tbl v w y)
          (ensures value_of i rho project tbl v w (App f [x; y]))
  = lemma_eval_bv_add tbl v w f x y;
    lemma_scoped_app f [x; y];
    lemma_scoped_cons x [y];
    lemma_scoped_cons y [];
    lemma_add i rho project f x y w

let rec lemma_eval_bv (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                      (tbl:leaf_table) (v:nat -> int) (w:pos) (e:expr)
  : Lemma (requires SM.ground_bv i project /\ SM.closed_ground e /\
                    agrees i rho project tbl v /\ Some? (eval_bv tbl v w e))
          (ensures get_sort e == BV.bv_sort w /\
                   project w (eval i e rho) == Some?.v (eval_bv tbl v w e))
          (decreases e)
  = match BV.numeral e with
    | Some (q, n) -> (match e with App f [] -> () | _ -> ())
    | None ->
      (match e with
       | App f [x] ->
         (match BV.extract_parts e, BV.zero_extend_parts e with
          | Some s, _ ->
            SM.lemma_ground_extract i rho project e s;
            lemma_eval_bv i rho project tbl v s.BV.source_width x
          | None, Some z ->
            SM.lemma_ground_zero_extend i rho project e z;
            lemma_eval_bv i rho project tbl v z.BV.input_width x
          | None, None -> lemma_leaf i rho project tbl v w e)
       | App f [x; y] ->
         (match BV.concat_parts e, BV.operation f [x; y] with
          | Some c, _ ->
            lemma_eval_bv_concat tbl v w f x y c;
            SM.lemma_ground_concat i rho project e c;
            lemma_eval_bv i rho project tbl v c.BV.left_width x;
            lemma_eval_bv i rho project tbl v c.BV.right_width y;
            lemma_concat_case i rho project tbl v w f x y c
          | None, Some (q, op) ->
            if q = w && op = BV.op_add then (
              lemma_eval_bv_add tbl v w f x y;
              lemma_scoped_app f [x; y];
              lemma_scoped_cons x [y];
              lemma_scoped_cons y [];
              lemma_eval_bv i rho project tbl v w x;
              lemma_eval_bv i rho project tbl v w y;
              lemma_add_case i rho project tbl v w f x y)
            else lemma_leaf i rho project tbl v w e
          | None, None -> lemma_leaf i rho project tbl v w e)
       | _ -> lemma_eval_bv_other tbl v w e; lemma_leaf i rho project tbl v w e)

(* The width of an evaluated bit-vector operator application is at most 4096,
   since every recognizer bounds it. *)
let lemma_bv_width (e:expr)
  : Lemma (requires Some? (bv_width e)) (ensures Some?.v (bv_width e) <= SM.max_width)
  = match e with
    | App f [] -> ()
    | App f [x] -> ()
    | App f [x; y] -> ()
    | _ -> ()

let lemma_equal_width (a b:expr)
  : Lemma (requires Some? (equal_width a b)) (ensures Some?.v (equal_width a b) <= SM.max_width)
  = match bv_width a with
    | Some _ -> lemma_bv_width a
    | None -> lemma_bv_width b

let lemma_bv_equality (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                      (tbl:leaf_table) (v:nat -> int) (w:pos) (a b:expr)
  : Lemma (requires SM.ground_bv i project /\ SM.closed_ground a /\ SM.closed_ground b /\
                    w <= SM.max_width /\ agrees i rho project tbl v /\
                    Some? (eval_bv tbl v w a) /\ Some? (eval_bv tbl v w b))
          (ensures (eval i a rho == eval i b rho) <==>
                   (Some?.v (eval_bv tbl v w a) = Some?.v (eval_bv tbl v w b)))
  = lemma_eval_bv i rho project tbl v w a;
    lemma_eval_bv i rho project tbl v w b;
    SM.lemma_ground_equal i rho project w a b

let lemma_unsigned (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                   (tbl:leaf_table) (v:nat -> int) (f:func_decl) (a b:expr)
  : Lemma (requires SM.ground_bv i project /\ SM.closed_ground (App f [a; b]) /\
                    agrees i rho project tbl v /\
                    Some? (BV.unsigned_parts (App f [a; b])) /\
                    (let c = Some?.v (BV.unsigned_parts (App f [a; b])) in
                     Some? (eval_bv tbl v c.BV.width a) /\ Some? (eval_bv tbl v c.BV.width b)))
          (ensures (let c = Some?.v (BV.unsigned_parts (App f [a; b])) in
                    eval i (App f [a; b]) rho ==
                    VBool (BV.unsigned_value c.BV.relation
                             (Some?.v (eval_bv tbl v c.BV.width a))
                             (Some?.v (eval_bv tbl v c.BV.width b)))))
  = let c = Some?.v (BV.unsigned_parts (App f [a; b])) in
    SM.lemma_ground_unsigned i rho project (App f [a; b]) c;
    assert (c.BV.lhs == a /\ c.BV.rhs == b);
    lemma_eval_bv i rho project tbl v c.BV.width a;
    lemma_eval_bv i rho project tbl v c.BV.width b

let rec lemma_eval_bool (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                        (tbl:leaf_table) (v:nat -> int) (e:expr)
  : Lemma (requires eval_model i project /\ SM.closed_ground e /\
                    agrees i rho project tbl v /\ Some? (eval_bool tbl v e))
          (ensures eval i e rho == VBool (Some?.v (eval_bool tbl v e)))
          (decreases e)
  = match e with
    | App f args ->
      assert (VBool? (eval i e rho));
      lemma_scoped_app f args;
      if C.canonical_true f && args = [] then ()
      else if C.canonical_false f && args = [] then ()
      else if C.canonical_not f then
        (match args with
         | [a] ->
           lemma_scoped_cons a [];
           lemma_eval_bool i rho project tbl v a)
      else if C.canonical_or f then lemma_eval_or i rho project tbl v args
      else if C.canonical_and f then lemma_eval_and i rho project tbl v args
      else if C.canonical_eq f then
        (match args with
         | [a; b] ->
           lemma_scoped_cons a [b];
           lemma_scoped_cons b [];
           if boolean_pair a b then (
             lemma_eval_bool i rho project tbl v a;
             lemma_eval_bool i rho project tbl v b)
           else (
             lemma_equal_width a b;
             lemma_bv_equality i rho project tbl v (Some?.v (equal_width a b)) a b))
      else
        (match args with
         | [a; b] -> lemma_unsigned i rho project tbl v f a b)

and lemma_eval_or (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                  (tbl:leaf_table) (v:nat -> int) (args:list expr)
  : Lemma (requires eval_model i project /\ SM.closed_args args /\
                    agrees i rho project tbl v /\ Some? (eval_or tbl v args))
          (ensures Some?.v (eval_or tbl v args) == true <==> clause_holds i rho args)
          (decreases args)
  = match args with
    | [] -> ()
    | a :: rest ->
      lemma_scoped_cons a rest;
      lemma_eval_bool i rho project tbl v a;
      lemma_eval_or i rho project tbl v rest

and lemma_eval_and (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                   (tbl:leaf_table) (v:nat -> int) (args:list expr)
  : Lemma (requires eval_model i project /\ SM.closed_args args /\
                    agrees i rho project tbl v /\ Some? (eval_and tbl v args))
          (ensures Some?.v (eval_and tbl v args) == true <==> conj_holds i rho args)
          (decreases args)
  = match args with
    | [] -> ()
    | a :: rest ->
      lemma_scoped_cons a rest;
      lemma_eval_bool i rho project tbl v a;
      lemma_eval_and i rho project tbl v rest

(* The values of the leaves in the model form one of the enumerated vectors. *)
let rec actual (i:interpretation value) (rho:env value) (project:pos -> value -> int)
               (tbl:leaf_table) : Tot (list int) (decreases tbl) =
  match tbl with
  | [] -> []
  | (e, w) :: rest -> project w (eval i e rho) :: actual i rho project rest

let rec lemma_actual_length (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                            (tbl:leaf_table)
  : Lemma (ensures L.length (actual i rho project tbl) == L.length tbl) (decreases tbl)
  = match tbl with
    | [] -> ()
    | _ :: rest -> lemma_actual_length i rho project rest

let rec lemma_actual_index (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                           (tbl:leaf_table) (k:nat)
  : Lemma (requires k < L.length tbl)
          (ensures L.length (actual i rho project tbl) == L.length tbl /\
                   L.index (actual i rho project tbl) k ==
                   project (snd (L.index tbl k)) (eval i (fst (L.index tbl k)) rho))
          (decreases tbl)
  = lemma_actual_length i rho project tbl;
    match tbl with
    | _ :: rest -> if k = 0 then () else lemma_actual_index i rho project rest (k - 1)

let rec lemma_actual_range (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                           (tbl:leaf_table)
  : Lemma (requires SM.ground_bv i project /\ L.for_all closed_leaf tbl)
          (ensures in_range (widths tbl) (actual i rho project tbl))
          (decreases tbl)
  = match tbl with
    | [] -> ()
    | (e, w) :: rest ->
      SM.lemma_ground_word i rho project w e;
      lemma_actual_range i rho project rest

let lemma_actual_agrees (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                        (tbl:leaf_table)
  : Lemma (agrees i rho project tbl (vector_value (actual i rho project tbl)))
  = let aux (k:nat)
      : Lemma (k < L.length tbl ==>
               vector_value (actual i rho project tbl) k ==
               project (snd (L.index tbl k)) (eval i (fst (L.index tbl k)) rho))
      = if k < L.length tbl then lemma_actual_index i rho project tbl k in
    FStar.Classical.forall_intro aux

let lemma_valid (i:interpretation value) (rho:env value) (project:pos -> value -> int) (e:expr)
  : Lemma (requires eval_model i project /\ valid e)
          (ensures lit_true i rho e)
  = let tbl = leaves_bool [] e in
    let r = actual i rho project tbl in
    lemma_actual_range i rho project tbl;
    lemma_for_all_vectors (widths tbl) (clause_true tbl e) r;
    lemma_actual_agrees i rho project tbl;
    lemma_eval_bool i rho project tbl (vector_value r) e

(* The accepted path is sound in every model of the ground contracts. *)
let lemma_valid_ground (e:expr) (i:interpretation value) (project:pos -> value -> int) (rho:env value)
  : Lemma (requires SM.ground_model i project /\ valid e) (ensures lit_true i rho e)
  = lemma_valid i rho project e

let lemma_equivalent_ground (a b:expr) (i:interpretation value) (project:pos -> value -> int)
                            (rho:env value)
  : Lemma (requires SM.ground_model i project /\ equivalent a b) (ensures eval i a rho == eval i b rho)
  = lemma_valid i rho project (mk_eq_expr a b);
    assert (C.canonical_eq (eq_decl (get_sort a)))

(* ... and those models exist: every standard interpretation, whatever the
   values of its opaque leaves, makes an accepted clause true. *)
let lemma_valid_standard (e:expr) (leaf:func_decl -> list value -> int) (rho:env value)
  : Lemma (requires valid e) (ensures lit_true (SM.standard leaf) rho e)
  = SM.lemma_standard_model leaf;
    lemma_valid (SM.standard leaf) rho SM.std_project e

let lemma_equivalent_standard (a b:expr) (leaf:func_decl -> list value -> int) (rho:env value)
  : Lemma (requires equivalent a b) (ensures eval (SM.standard leaf) a rho == eval (SM.standard leaf) b rho)
  = SM.lemma_standard_model leaf;
    lemma_equivalent_ground a b (SM.standard leaf) SM.std_project rho

(* The kernel's entry points. The hypotheses are conjuncts of
   `Z3UnifiedProof.model_sound` (the bit-vector one through
   `Z3TheoryNormalize.normalization_model`); they imply the ground
   contracts (`Z3StandardModel.lemma_ground_of_global`). *)
let lemma_valid_sound (e:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (project:pos -> value -> int). BV.bv_model i project) /\
                    boolean_model i /\ not_sound i /\ and_sound i /\ or_sound i /\ implies_sound i /\
                    eq_sound i /\ true_sound i /\ false_sound i /\ valid e)
          (ensures lit_true i rho e)
  = let aux (project:pos -> value -> int)
      : Lemma (requires BV.bv_model i project) (ensures lit_true i rho e)
      = SM.lemma_ground_of_global i project;
        lemma_valid i rho project e in
    FStar.Classical.exists_elim (lit_true i rho e)
      #(pos -> value -> int) #(fun project -> BV.bv_model i project) () (fun project -> aux project)

let lemma_equivalent_sound (a b:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (project:pos -> value -> int). BV.bv_model i project) /\
                    boolean_model i /\ not_sound i /\ and_sound i /\ or_sound i /\ implies_sound i /\
                    eq_sound i /\ true_sound i /\ false_sound i /\ equivalent a b)
          (ensures eval i a rho == eval i b rho)
  = lemma_valid_sound (mk_eq_expr a b) i rho
