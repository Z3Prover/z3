module Z3BvAddNormalize

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module D = Z3Definitions
module L = FStar.List.Tot
module U = FStar.UInt
module M = FStar.Math.Lemmas
module BV = Z3BvLemma
module BX = Z3BvExtract

(* Modular normalization of bit-vector sums over opaque summands.

   The bit-vector rewriter flattens `bvadd`, adds up its numerals into one, and keeps the other summands.
   A rewrite such as `bvadd(bvadd(2, t), 1) = bvadd(3, t)` therefore holds for every term `t`, however wide.

   Both sides of an equation `a = b` of sort `BV<w>` are read as sums. A summand is a numeral, a nested
   `bvadd` (binary or n-ary, recognized by `Z3BvExtract.arith` from the declaration kind, its parameter
   and its argument sorts), or any other closed term of sort `BV<w>`, which is kept as an opaque atom. A
   side is thus the sum of its numerals, taken modulo 2^w, and the sequence of its atoms, in the order
   in which they occur. The step is accepted when both sides have the same width, the same numeral total
   modulo 2^w and the same atoms in the same order. An atom is never evaluated: it is only required to
   be the same term on both sides, so it has the same value there whatever that value is.

   A declaration of the kinds read here (a numeral or `bvadd`) that fails its recognizer is malformed and
   is not an atom; the step stays pending. The tree has at most `max_nodes` occurrences, counted on the
   tree so that a shared DAG cannot hide its size, before anything else is done. Everything outside this
   shape leaves the step pending, never rejected. *)

let max_nodes : nat = 512

(* The width of a `bvadd` application: binary or n-ary, and not `bvmul`. *)
let add_width (f:func_decl) (args:list expr) : option pos =
  match BX.arith f args with
  | Some (w, op) -> if op = BV.op_add then Some w else None
  | None -> None

(* The declaration kinds that are read here; one that is not recognized is not an atom. *)
let reserved (f:func_decl) : bool = f.interp = Some BV.op_numeral || f.interp = Some BV.op_add

(* The numeral total and the atoms of a term of sort `BV<w>`. *)
let rec summands (w:pos) (e:expr) : Tot (option (int & list expr)) (decreases e) =
  match BV.numeral e with
  | Some (q, n) -> if q = w then Some (n, []) else None
  | None ->
    (match e with
     | App f args ->
       (match add_width f args with
        | Some q -> if q = w then summands_args w args else None
        | None -> if reserved f || get_sort e <> BV.bv_sort w then None else Some (0, [e]))
     | _ -> None)

and summands_args (w:pos) (args:list expr) : Tot (option (int & list expr)) (decreases args) =
  match args with
  | [] -> Some (0, [])
  | a :: rest ->
    (match summands w a, summands_args w rest with
     | Some (n, xs), Some (m, ys) -> Some (n + m, L.append xs ys)
     | _, _ -> None)

(* The width of one side that is a numeral or a sum; a side that is another term has no width of its own. *)
let own_width (e:expr) : option pos =
  match BV.numeral e with
  | Some (w, _) -> Some w
  | None -> (match e with App f args -> add_width f args | _ -> None)

let common_width (a b:expr) : option pos =
  match own_width a with
  | Some w -> Some w
  | None -> own_width b

let same_sum (w:pos) (a b:expr) : bool =
  match summands w a, summands w b with
  | Some (n, xs), Some (m, ys) -> n % pow2 w = m % pow2 w && xs = ys
  | _, _ -> false

(* The size bound is tested first and guards the rest, as a conditional so that the order also holds under
   normalization. *)
let equivalent (a b:expr) : bool =
  if not (Some? (expression_budget max_nodes a) && Some? (expression_budget max_nodes b)) then false
  else if not (D.scoped [] a && D.scoped [] b) then false
  else match common_width a b with
       | Some w -> same_sum w a b
       | None -> false

(* --- Soundness ------------------------------------------------------ *)

(* The sum of the values of the atoms in the model. *)
let rec atom_total (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                   (w:pos) (atoms:list expr) : Tot int (decreases atoms) =
  match atoms with
  | [] -> 0
  | a :: rest -> project w (eval i a rho) + atom_total i rho project w rest

let rec lemma_atom_total_append (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                                (w:pos) (xs ys:list expr)
  : Lemma (ensures atom_total i rho project w (L.append xs ys) ==
                   atom_total i rho project w xs + atom_total i rho project w ys)
          (decreases xs)
  = match xs with
    | [] -> ()
    | _ :: rest -> lemma_atom_total_append i rho project w rest ys

(* Residues add: if a = x and b = y modulo p, then (a + b) = (x + y) modulo p. *)
let lemma_add_residues (p:pos) (a b x y:int)
  : Lemma (requires a % p == x % p /\ b % p == y % p)
          (ensures (a + b) % p == (x + y) % p)
  = M.lemma_mod_plus_distr_l a b p;
    M.lemma_mod_plus_distr_r (a % p) b p;
    M.lemma_mod_plus_distr_l x y p;
    M.lemma_mod_plus_distr_r (x % p) y p

let lemma_scoped_app (f:func_decl) (args:list expr)
  : Lemma (requires D.scoped [] (App f args)) (ensures D.scoped_args [] args)
  = ()

let lemma_scoped_cons (a:expr) (rest:list expr)
  : Lemma (requires D.scoped_args [] (a :: rest)) (ensures D.scoped [] a /\ D.scoped_args [] rest)
  = ()

(* What the model says about a term whose sum reading is (n, atoms). *)
let value_of (i:interpretation value) (rho:env value) (project:pos -> value -> int)
             (w:pos) (e:expr) (n:int) (atoms:list expr) : prop =
  get_sort e == BV.bv_sort w /\
  project w (eval i e rho) == (n + atom_total i rho project w atoms) % pow2 w

let lemma_words_cons (w:pos) (project:pos -> value -> int) (v:value) (vs:list value)
  : Lemma (BV.words w project (v :: vs) == U.to_uint_t w (project w v) :: BV.words w project vs)
  = ()

(* One step of the right fold of an n-ary sum. *)
let lemma_nary_step (w:pos) (x:U.uint_t w) (ys:list (U.uint_t w))
  : Lemma (requires Cons? ys)
          (ensures BV.calculate_nary w BV.op_add (x :: ys) == U.add_mod x (BV.calculate_nary w BV.op_add ys))
  = match ys with
    | _ :: _ -> ()

let rec lemma_summands (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                       (w:pos) (e:expr) (n:int) (atoms:list expr)
  : Lemma (requires BV.bv_model i project /\ D.scoped [] e /\ summands w e == Some (n, atoms))
          (ensures value_of i rho project w e n atoms)
          (decreases e)
  = match BV.numeral e with
    | Some (q, k) ->
      (match e with
       | App f [] -> M.small_mod k (pow2 w)
       | _ -> ())
    | None ->
      (match e with
       | App f args ->
         (match add_width f args with
          | Some q ->
            lemma_scoped_app f args;
            BX.lemma_arith i rho project f args w BV.op_add;
            lemma_summands_args i rho project w args n atoms
          | None ->
            BV.lemma_word i rho project w e;
            M.small_mod (project w (eval i e rho)) (pow2 w))
       | _ -> ())

and lemma_summands_args (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                        (w:pos) (args:list expr) (n:int) (atoms:list expr)
  : Lemma (requires BV.bv_model i project /\ D.scoped_args [] args /\ Cons? args /\
                    summands_args w args == Some (n, atoms))
          (ensures BV.calculate_nary w BV.op_add (BV.words w project (eval_args i args rho)) ==
                   (n + atom_total i rho project w atoms) % pow2 w)
          (decreases args)
  = match args with
    | x :: rest ->
      lemma_scoped_cons x rest;
      (match summands w x, summands_args w rest with
       | Some (n1, as1), Some (m, ys) ->
         lemma_summands i rho project w x n1 as1;
         BV.lemma_word i rho project w x;
         lemma_atom_total_append i rho project w as1 ys;
         lemma_words_cons w project (eval i x rho) (eval_args i rest rho);
         (match rest with
          | [] -> ()
          | y :: rest' ->
            lemma_summands_args i rho project w rest m ys;
            lemma_words_cons w project (eval i y rho) (eval_args i rest' rho);
            lemma_nary_step w (U.to_uint_t w (project w (eval i x rho)))
              (BV.words w project (eval_args i rest rho));
            lemma_add_residues (pow2 w) (project w (eval i x rho))
              (BV.calculate_nary w BV.op_add (BV.words w project (eval_args i rest rho)))
              (n1 + atom_total i rho project w as1) (m + atom_total i rho project w ys))
       | _, _ -> ())

let lemma_equivalent (a b:expr) (i:interpretation value) (rho:env value) (project:pos -> value -> int)
  : Lemma (requires BV.bv_model i project /\ equivalent a b)
          (ensures eval i a rho == eval i b rho)
  = let w = Some?.v (common_width a b) in
    let (n, xs) = Some?.v (summands w a) in
    let (m, ys) = Some?.v (summands w b) in
    lemma_summands i rho project w a n xs;
    lemma_summands i rho project w b m ys;
    lemma_add_residues (pow2 w) n (atom_total i rho project w xs) m (atom_total i rho project w ys);
    BV.lemma_reflect i rho project w a b

(* The hypothesis is a conjunct of `Z3UnifiedProof.model_sound`, reached through
   `Z3TheoryNormalize.normalization_model`. *)
let lemma_equivalent_sound (a b:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (project:pos -> value -> int). BV.bv_model i project) /\ equivalent a b)
          (ensures eval i a rho == eval i b rho)
  = let aux (project:pos -> value -> int)
      : Lemma (requires BV.bv_model i project) (ensures eval i a rho == eval i b rho)
      = lemma_equivalent a b i rho project in
    FStar.Classical.exists_elim (eval i a rho == eval i b rho)
      #(pos -> value -> int) #(fun project -> BV.bv_model i project) () (fun project -> aux project)
