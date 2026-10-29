(*
   Z3FiniteFieldPac.fst

   Replays the polynomial ideal certificate that Z3's finite-field solver
   records with a theory lemma,

     ((_ th-lemma ff pac (ff-pac (ff-premises L0 ... Ln) ROOT (ff-support i ...))) C)

   (`src/ast/ff/ff_evidence.cpp`, `pack_certificate`). The native bridge
   flattens the certificate DAG into `certificate`: the premise literals, the
   nodes in topological order with integer references, the root and the
   support indices. Nothing marshalled is trusted:

   * The input table is re-derived here from the premise ASTs, in the
     producer's order (`encoding::bind`/`encoding::term`): for every premise
     `(= a b)` or `(not (= a b))` over one `FF<p>`, the subterms of `a` and
     then of `b` are visited (arguments right to left, each term once); a
     numeral is a constant, a field operation `ff.add`/`ff.mul`/`ff.bitsum`/
     `ff.neg` gets a fresh variable `v` and the definition `v - op(args)`,
     any other term is an opaque variable. A positive premise contributes
     `a - b`. A negated premise allocates the producer's inverse witness and
     contributes an equation that is never usable here: replaying it needs
     inverses, i.e. that `p` is prime. The producer's Fermat equations
     `x^p - x` (fields up to 31) are not generated, so inputs naming them are
     out of range.
   * Every node must refer to strictly earlier nodes, so the DAG has no cycle
     and no future or missing reference. `ff-mul` coefficients must be
     canonical numerals of the same `FF<p>`, and factors sorted variables of
     the table. Polynomial sizes and the cumulative work are bounded before
     each operation.
   * Each used input must be a definition or a positive premise in the
     support whose negation is a literal of the conclusion, the support must
     be strictly increasing, in range and exactly the set of used premises,
     and the root must normalise to the constant 1.

   Soundness (`lemma_check_sound`). Give every variable the residue of its
   term. Under `ff_model` every definition evaluates to 0 modulo p, and a
   positive premise does when it holds. If the conclusion were false, every
   used premise would hold, so every node, being a sum or a monomial multiple
   of earlier nodes, would evaluate to 0 modulo p, but the root evaluates to
   1 and p >= 2. Only the commutative-ring laws of Z/pZ are used: neither
   primality of p nor the claimed result is assumed, and `ff_model` is the
   unchanged trust statement of `Z3FiniteFieldLemma`.
*)
module Z3FiniteFieldPac

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ProofIndex
module FF = Z3FiniteFieldLemma
module D = Z3Definitions
module L = FStar.List.Tot
module M = FStar.Math.Lemmas
module O = Z3ObservationalEquality
module PT = Z3ProofTheory
module C = Z3CanonicalOps

(* ----------------------------------------------------------------- *)
(* Certificates                                                        *)
(* ----------------------------------------------------------------- *)

type pac_node =
  | PacInput : index:int -> pac_node
  | PacAdd : left:int -> right:int -> pac_node
  | PacMul : source:int -> coefficient:expr -> factor:list int -> pac_node

type certificate = {
  pac_premises: list expr;
  pac_nodes: list pac_node;
  pac_root: int;
  pac_support: list int;
}

(* The producer's own bounds on the table, and bounds on the replay. *)
let max_premises : nat = 4096
let max_variables : nat = 4096
let max_equations : nat = 8192
let max_nodes : nat = 100000
let max_poly_size : nat = 16384
let max_work : nat = 4000000

(* ----------------------------------------------------------------- *)
(* The input table                                                     *)
(* ----------------------------------------------------------------- *)

type origin =
  | Definition
  | Premise : index:nat -> literal:expr -> origin
  | Witness

type equation = FF.poly & origin

(* Variable k stands for the k-th term; equations are kept newest first. *)
type encoding = {
  terms: list expr;
  equations: list equation;
  count: nat;
}

let empty_encoding : encoding = { terms = []; equations = []; count = 0 }

let term_poly (p:int) (tbl:list expr) (t:expr) : option FF.poly =
  match FF.numeral t with
  | Some (q, n) -> if q = p then Some [([], n)] else None
  | None ->
    (match FF.index_of t tbl with
     | Some k -> Some [([k], 1)]
     | None -> None)

let rec term_polys (p:int) (tbl:list expr) (ts:list expr)
  : Tot (option (list FF.poly)) (decreases ts) =
  match ts with
  | [] -> Some []
  | t :: rest ->
    (match term_poly p tbl t, term_polys p tbl rest with
     | Some q, Some qs -> Some (q :: qs)
     | _, _ -> None)

let allocate (st:encoding) (t:expr) : option encoding =
  if L.length st.terms + 1 > max_variables then None
  else Some { st with terms = L.append st.terms [t] }

let push (st:encoding) (e:equation) : option encoding =
  if st.count + 1 > max_equations then None
  else Some { st with equations = e :: st.equations; count = st.count + 1 }

let definition (k:nat) (f:FF.poly) : FF.poly = FF.padd [([k], 1)] (FF.pscale (-1) f)

let define (st:encoding) (t:expr) (f:FF.poly) : option encoding =
  let k = L.length st.terms in
  match allocate st t with
  | Some st1 -> push st1 (definition k f, Definition)
  | None -> None

let rec visit (p:int) (st:encoding) (t:expr) : Tot (option encoding) (decreases t) =
  match FF.numeral t with
  | Some (q, _) -> if q = p then Some st else None
  | None ->
    if Some? (FF.index_of t st.terms) then Some st
    else if get_sort t <> FF.ff_sort p then None
    else
      match t with
      | App f args ->
        (match FF.operation f args with
         | Some (q, op) ->
           if q <> p then None
           else
             (match visit_args p st args with
              | None -> None
              | Some st1 ->
                (match term_polys p st1.terms args with
                 | None -> None
                 | Some qs ->
                   (match FF.combine op qs with
                    | None -> None
                    | Some f -> define st1 t f)))
         | None -> allocate st t)
      | _ -> None

(* Right to left, as the producer pops its work stack. *)
and visit_args (p:int) (st:encoding) (args:list expr)
  : Tot (option encoding) (decreases args) =
  match args with
  | [] -> Some st
  | a :: rest ->
    (match visit_args p st rest with
     | None -> None
     | Some st1 -> visit p st1 a)

let premise_parts (p:int) (l:expr) : option (bool & expr & expr) =
  let positive, atom =
    match PT.is_not l with
    | Some a -> false, a
    | None -> true, l in
  match FF.eq_parts atom with
  | Some (a, b) -> if FF.closed_ff p a && FF.closed_ff p b then Some (positive, a, b) else None
  | None -> None

let premise_equation (p:int) (k:nat) (l a b:expr) (st:encoding) (positive:bool) : option encoding =
  if positive then
    (match term_poly p st.terms a, term_poly p st.terms b with
     | Some qa, Some qb -> push st (FF.padd qa (FF.pscale (-1) qb), Premise k l)
     | _, _ -> None)
  else
    (match allocate st l with
     | Some st1 -> push st1 ([], Witness)
     | None -> None)

let rec bind (p:int) (k:nat) (st:encoding) (ps:list expr) : Tot (option encoding) (decreases ps) =
  match ps with
  | [] -> Some st
  | l :: rest ->
    (match premise_parts p l with
     | None -> None
     | Some (positive, a, b) ->
       (match visit p st a with
        | None -> None
        | Some st1 ->
          (match visit p st1 b with
           | None -> None
           | Some st2 ->
             (match premise_equation p k l a b st2 positive with
              | None -> None
              | Some st3 -> bind p (k + 1) st3 rest))))

(* Equation j (in producer order) at key j; the list is newest first. *)
let rec index_equations (tree:index_tree equation) (k:int) (es:list equation)
  : Tot (index_tree equation) (decreases es) =
  match es with
  | [] -> tree
  | e :: rest -> if k < 0 then tree else index_equations (index_put tree k e) (k - 1) rest

(* ----------------------------------------------------------------- *)
(* Replaying the certificate                                           *)
(* ----------------------------------------------------------------- *)

let clause_literals (e:expr) : list expr =
  match e with
  | App f args -> if C.canonical_or f then args else [e]
  | _ -> [e]

let rec negated_in (l:expr) (lits:list expr) : Tot bool (decreases lits) =
  match lits with
  | [] -> false
  | x :: rest -> PT.is_not x = Some l || negated_in l rest

(* Strictly increasing indices below n. *)
let rec support_tree (n:int) (previous:int) (tree:index_tree bool) (s:list int)
  : Tot (option (index_tree bool)) (decreases s) =
  match s with
  | [] -> Some tree
  | k :: rest ->
    if 0 <= k && previous < k && k < n then support_tree n k (index_put tree k true) rest else None

let rec all_used (used:index_tree bool) (s:list int) : Tot bool (decreases s) =
  match s with
  | [] -> true
  | k :: rest -> k >= 0 && index_get used k = Some true && all_used used rest

(* Sorted variables below n; repetitions are powers. *)
let rec variables (n:nat) (previous:int) (fs:list int) : Tot (option (list nat)) (decreases fs) =
  match fs with
  | [] -> Some []
  | f :: rest ->
    if 0 <= f && previous <= f && f < n
    then (match variables n f rest with Some vs -> Some (f :: vs) | None -> None)
    else None

let rec size (q:FF.poly) : Tot nat (decreases q) =
  match q with
  | [] -> 0
  | (m, _) :: rest -> 1 + L.length m + size rest

let rec scale_mono (m:FF.mono) (c:int) (q:FF.poly) : Tot FF.poly (decreases q) =
  match q with
  | [] -> []
  | (m2, c2) :: rest -> (FF.mono_mul m m2, c * c2) :: scale_mono m c rest

(* Canonical form: merge sort on monomials, coefficients reduced modulo p,
   zero terms dropped. Only evaluation modulo p matters for soundness. *)
#push-options "--fuel 2"
let rec split (q:FF.poly)
  : Tot (r:(FF.poly & FF.poly){L.length (fst r) + L.length (snd r) == L.length q /\
                               (L.length q >= 2 ==>
                                (L.length (fst r) < L.length q /\ L.length (snd r) < L.length q))})
        (decreases q) =
  match q with
  | x :: y :: rest -> let (a, b) = split rest in (x :: a, y :: b)
  | _ -> (q, [])
#pop-options

let rec canon (q:FF.poly) : Tot FF.poly (decreases (L.length q)) =
  if L.length q < 2 then q
  else let (a, b) = split q in FF.padd (canon a) (canon b)

let rec reduce (p:pos) (q:FF.poly) : Tot FF.poly (decreases q) =
  match q with
  | [] -> []
  | (m, c) :: rest -> if c % p = 0 then reduce p rest else (m, c % p) :: reduce p rest

let normalize (p:pos) (q:FF.poly) : FF.poly = reduce p (canon q)

noeq
type replay = {
  values: index_tree FF.poly;
  next: nat;
  work: nat;
  used: index_tree bool;
}

let initial_replay : replay = { values = Empty; next = 0; work = 0; used = Empty }

let earlier (r:replay) (j:int) : option FF.poly =
  if 0 <= j && j < r.next then index_get r.values j else None

let record (p:pos) (r:replay) (cost:nat) (q:FF.poly) (used:index_tree bool) : option replay =
  Some { values = index_put r.values r.next (normalize p q); next = r.next + 1;
         work = r.work + cost; used = used }

let step (p:pos) (nvars:nat) (eqs:index_tree equation) (sup:index_tree bool)
         (lits:list expr) (r:replay) (n:pac_node) : option replay =
  match n with
  | PacInput j ->
    if j < 0 then None
    else
      (match index_get eqs j with
       | Some (q, Definition) ->
         if r.work + size q > max_work then None else record p r (size q) q r.used
       | Some (q, Premise k l) ->
         if index_get sup k = Some true && negated_in l lits && r.work + size q <= max_work
         then record p r (size q) q (index_put r.used k true)
         else None
       | _ -> None)
  | PacAdd a b ->
    (match earlier r a, earlier r b with
     | Some qa, Some qb ->
       let cost = size qa + size qb in
       if cost > max_poly_size || r.work + cost > max_work then None
       else record p r cost (FF.padd qa qb) r.used
     | _, _ -> None)
  | PacMul s c fs ->
    (match earlier r s, FF.numeral c, variables nvars 0 fs with
     | Some q, Some (pc, k), Some vs ->
       let cost = size q + L.length q * L.length vs in
       if pc <> p || cost > max_poly_size || r.work + cost > max_work then None
       else record p r cost (scale_mono vs k q) r.used
     | _, _, _ -> None)

let rec replay_nodes (p:pos) (nvars:nat) (eqs:index_tree equation) (sup:index_tree bool)
                     (lits:list expr) (r:replay) (ns:list pac_node)
  : Tot (option replay) (decreases ns) =
  match ns with
  | [] -> Some r
  | n :: rest ->
    (match step p nvars eqs sup lits r n with
     | Some r' -> replay_nodes p nvars eqs sup lits r' rest
     | None -> None)

let unit_root (r:replay) (root:int) : bool =
  0 <= root && root < r.next && index_get r.values root = Some [([], 1)]

let check (c:certificate) (e:expr) : bool =
  let n = L.length c.pac_premises in
  if n = 0 || n > max_premises || L.length c.pac_nodes > max_nodes then false
  else
    match FF.find_modulus_args c.pac_premises with
    | None -> false
    | Some p ->
      if p < 2 then false
      else
        match bind p 0 empty_encoding c.pac_premises, support_tree n (-1) Empty c.pac_support with
        | Some st, Some sup ->
          let eqs = index_equations Empty (L.length st.equations - 1) st.equations in
          (match replay_nodes p (L.length st.terms) eqs sup (clause_literals e)
                   initial_replay c.pac_nodes with
           | Some r -> unit_root r c.pac_root && all_used r.used c.pac_support
           | None -> false)
        | _, _ -> false

let lemma_check_bounds (c:certificate) (e:expr)
  : Lemma (requires check c e)
          (ensures 1 <= L.length c.pac_premises /\ L.length c.pac_premises <= max_premises /\
                   L.length c.pac_nodes <= max_nodes)
  = ()

(* ----------------------------------------------------------------- *)
(* Polynomial lemmas                                                   *)
(* ----------------------------------------------------------------- *)

#push-options "--fuel 2"
let rec lemma_split (v:nat -> int) (q:FF.poly)
  : Lemma (ensures FF.peval v (fst (split q)) + FF.peval v (snd (split q)) == FF.peval v q)
          (decreases q)
  = match q with
    | x :: y :: rest -> lemma_split v rest
    | _ -> ()
#pop-options

let rec lemma_canon (v:nat -> int) (q:FF.poly)
  : Lemma (ensures FF.peval v (canon q) == FF.peval v q) (decreases (L.length q))
  = if L.length q < 2 then ()
    else (
      let (a, b) = split q in
      lemma_split v q;
      lemma_canon v a;
      lemma_canon v b;
      FF.lemma_padd v (canon a) (canon b))

let rec lemma_reduce (v:nat -> int) (p:pos) (q:FF.poly)
  : Lemma (ensures FF.peval v (reduce p q) % p == FF.peval v q % p) (decreases q)
  = match q with
    | [] -> ()
    | (m, c) :: rest ->
      lemma_reduce v p rest;
      M.lemma_mod_mul_distr_l c (FF.mval v m) p;
      if c % p = 0
      then FF.lemma_add_cong p (c * FF.mval v m) (FF.peval v rest) 0 (FF.peval v (reduce p rest))
      else (
        M.lemma_mod_mul_distr_l (c % p) (FF.mval v m) p;
        M.lemma_mod_twice c p;
        FF.lemma_add_cong p ((c % p) * FF.mval v m) (FF.peval v (reduce p rest))
                            (c * FF.mval v m) (FF.peval v rest))

let lemma_normalize (v:nat -> int) (p:pos) (q:FF.poly)
  : Lemma (FF.peval v (normalize p q) % p == FF.peval v q % p)
  = lemma_canon v q;
    lemma_reduce v p (canon q)

let rec lemma_scale_mono (v:nat -> int) (m:FF.mono) (c:int) (q:FF.poly)
  : Lemma (ensures FF.peval v (scale_mono m c q) == (c * FF.mval v m) * FF.peval v q)
          (decreases q)
  = match q with
    | [] -> ()
    | (m2, c2) :: rest ->
      lemma_scale_mono v m c rest;
      FF.lemma_mval_mul v m m2;
      FF.lemma_mul4 c c2 (FF.mval v m) (FF.mval v m2);
      M.distributivity_add_right (c * FF.mval v m) (c2 * FF.mval v m2) (FF.peval v rest)

let lemma_zero_product (p:pos) (a b:int)
  : Lemma (requires b % p == 0) (ensures (a * b) % p == 0)
  = M.lemma_mod_mul_distr_r a b p

let lemma_zero_sum (p:pos) (a b:int)
  : Lemma (requires a % p == 0 /\ b % p == 0) (ensures (a + b) % p == 0)
  = FF.lemma_add_cong p a b 0 0

#push-options "--fuel 2"
let lemma_peval_constant (v:nat -> int) (n:int) : Lemma (FF.peval v [([], n)] == n) = ()
let lemma_peval_variable (v:nat -> int) (k:nat) : Lemma (FF.peval v [([k], 1)] == v k) = ()
#pop-options

(* ----------------------------------------------------------------- *)
(* Table prefixes                                                      *)
(* ----------------------------------------------------------------- *)

let rec prefix (a b:list expr) : Tot bool (decreases a) =
  match a, b with
  | [], _ -> true
  | x :: a', y :: b' -> x = y && prefix a' b'
  | _, _ -> false

let rec lemma_prefix_refl (a:list expr) : Lemma (ensures prefix a a) (decreases a) =
  match a with [] -> () | _ :: rest -> lemma_prefix_refl rest

let rec lemma_prefix_trans (a b c:list expr)
  : Lemma (requires prefix a b /\ prefix b c) (ensures prefix a c) (decreases a)
  = match a, b, c with
    | _ :: a', _ :: b', _ :: c' -> lemma_prefix_trans a' b' c'
    | _, _, _ -> ()

let rec lemma_prefix_append (a:list expr) (t:expr)
  : Lemma (ensures prefix a (L.append a [t])) (decreases a)
  = match a with [] -> () | _ :: rest -> lemma_prefix_append rest t

let rec lemma_prefix_index (a b:list expr) (k:nat)
  : Lemma (requires prefix a b /\ k < L.length a)
          (ensures k < L.length b /\ L.index b k == L.index a k)
          (decreases a)
  = match a, b with
    | _ :: a', _ :: b' -> if k = 0 then () else lemma_prefix_index a' b' (k - 1)

let rec lemma_append_last (a:list expr) (t:expr)
  : Lemma (ensures L.length (L.append a [t]) == L.length a + 1 /\
                   L.index (L.append a [t]) (L.length a) == t)
          (decreases a)
  = match a with [] -> () | _ :: rest -> lemma_append_last rest t

(* ----------------------------------------------------------------- *)
(* Soundness of the input table                                        *)
(* ----------------------------------------------------------------- *)

let valuation (i:interpretation value) (rho:env value) (project:int -> value -> int)
              (p:int) (tbl:list expr) : nat -> int =
  FF.valuation i rho project p tbl

let eq_ok (i:interpretation value) (rho:env value) (v:nat -> int) (p:pos) (e:equation) : prop =
  match e with
  | (q, Definition) -> FF.peval v q % p == 0
  | (q, Premise _ l) -> get_sort l == bool_sort /\ (lit_true i rho l ==> FF.peval v q % p == 0)
  | (_, Witness) -> True

let rec eqs_ok (i:interpretation value) (rho:env value) (v:nat -> int) (p:pos) (es:list equation)
  : Tot prop (decreases es) =
  match es with
  | [] -> True
  | e :: rest -> eq_ok i rho v p e /\ eqs_ok i rho v p rest

let lemma_term_poly (i:interpretation value) (rho:env value) (project:int -> value -> int)
                    (p:pos) (tbl final:list expr) (t:expr) (q:FF.poly)
  : Lemma (requires FF.ff_model i project /\ p >= 2 /\ D.scoped [] t /\ get_sort t == FF.ff_sort p /\
                    prefix tbl final /\ term_poly p tbl t == Some q)
          (ensures FF.peval (valuation i rho project p final) q % p == project p (eval i t rho))
  = let v = valuation i rho project p final in
    FF.lemma_range i rho project p t;
    M.small_mod (project p (eval i t rho)) p;
    match FF.numeral t with
    | Some (_, n) -> lemma_peval_constant v n
    | None ->
      let k = Some?.v (FF.index_of t tbl) in
      FF.lemma_index_of t tbl k;
      lemma_prefix_index tbl final k;
      lemma_peval_variable v k

let rec lemma_term_polys (i:interpretation value) (rho:env value) (project:int -> value -> int)
                         (p:pos) (tbl final:list expr) (args:list expr) (qs:list FF.poly)
  : Lemma (requires FF.ff_model i project /\ p >= 2 /\ D.scoped_args [] args /\
                    sorts_match args (FF.ff_domain p args) /\
                    prefix tbl final /\ term_polys p tbl args == Some qs)
          (ensures FF.match_list (valuation i rho project p final) p qs
                                 (FF.projections i rho project p args))
          (decreases args)
  = match args, qs with
    | a :: rest, q :: qs' ->
      FF.lemma_scoped_cons a rest;
      FF.lemma_sort_eq_base (get_sort a) ("FF" ^ Prims.string_of_int p);
      lemma_term_poly i rho project p tbl final a q;
      lemma_term_polys i rho project p tbl final rest qs'
    | _, _ -> ()
let rec lemma_projections_length (i:interpretation value) (rho:env value)
                                 (project:int -> value -> int) (p:int) (args:list expr)
  : Lemma (ensures L.length (FF.projections i rho project p args) == L.length args)
          (decreases args)
  = match args with
    | [] -> ()
    | _ :: rest -> lemma_projections_length i rho project p rest


let lemma_definition (i:interpretation value) (rho:env value) (project:int -> value -> int)
                     (p:pos) (tbl final:list expr) (f:func_decl) (args:list expr) (op:decl_kind)
                     (qs:list FF.poly) (fq:FF.poly)
  : Lemma (requires FF.ff_model i project /\ p >= 2 /\ D.scoped [] (App f args) /\
                    FF.operation f args == Some (p, op) /\
                    prefix tbl final /\ L.length tbl < L.length final /\
                    L.index final (L.length tbl) == App f args /\
                    term_polys p tbl args == Some qs /\ FF.combine op qs == Some fq)
          (ensures FF.peval (valuation i rho project p final) (definition (L.length tbl) fq) % p == 0)
  = let t = App f args in
    let v = valuation i rho project p final in
    let k = L.length tbl in
    let xs = FF.projections i rho project p args in
    FF.lemma_operation_shape f args p op;
    FF.lemma_scoped_app f args;
    lemma_term_polys i rho project p tbl final args qs;
    lemma_projections_length i rho project p args;
    FF.lemma_combine v p op qs xs fq;
    assert (project p (eval i t rho) == FF.calculate p op xs);
    FF.lemma_range i rho project p t;
    M.small_mod (project p (eval i t rho)) p;
    assert (v k == project p (eval i t rho));
    lemma_peval_variable v k;
    FF.lemma_pscale v (-1) fq;
    FF.lemma_padd v [([k], 1)] (FF.pscale (-1) fq);
    FF.lemma_same_mod_diff p (v k) (FF.peval v fq)

let lemma_premise (i:interpretation value) (rho:env value) (project:int -> value -> int)
                  (p:pos) (tbl final:list expr) (l a b:expr) (qa qb:FF.poly)
  : Lemma (requires FF.ff_model i project /\ eq_sound i /\ p >= 2 /\
                    FF.eq_parts l == Some (a, b) /\ FF.closed_ff p a /\ FF.closed_ff p b /\
                    prefix tbl final /\ term_poly p tbl a == Some qa /\ term_poly p tbl b == Some qb)
          (ensures eq_ok i rho (valuation i rho project p final) p
                     (FF.padd qa (FF.pscale (-1) qb), Premise 0 l))
  = let v = valuation i rho project p final in
    lemma_term_poly i rho project p tbl final a qa;
    lemma_term_poly i rho project p tbl final b qb;
    FF.lemma_pscale v (-1) qb;
    FF.lemma_padd v qa (FF.pscale (-1) qb);
    match l with
    | App f [_; _] ->
      assert (f.decl_name == "=");
      if FF.peval v qa % p = FF.peval v qb % p
      then FF.lemma_same_mod_diff p (FF.peval v qa) (FF.peval v qb)

let lemma_eq_ok_index (i:interpretation value) (rho:env value) (v:nat -> int) (p:pos)
                      (q:FF.poly) (k k':nat) (l:expr)
  : Lemma (requires eq_ok i rho v p (q, Premise k l)) (ensures eq_ok i rho v p (q, Premise k' l))
  = ()

let rec lemma_visit (i:interpretation value) (rho:env value) (project:int -> value -> int)
                    (p:pos) (st:encoding) (t:expr) (st':encoding) (final:list expr)
  : Lemma (requires FF.ff_model i project /\ p >= 2 /\ D.scoped [] t /\
                    visit p st t == Some st' /\ prefix st'.terms final)
          (ensures prefix st.terms st'.terms /\
                   (eqs_ok i rho (valuation i rho project p final) p st.equations ==>
                    eqs_ok i rho (valuation i rho project p final) p st'.equations))
          (decreases t)
  = match FF.numeral t with
    | Some _ -> lemma_prefix_refl st.terms
    | None ->
      if Some? (FF.index_of t st.terms) then lemma_prefix_refl st.terms
      else
        match t with
        | App f args ->
          (match FF.operation f args with
           | Some (q, op) ->
             let st1 = Some?.v (visit_args p st args) in
             let qs = Some?.v (term_polys p st1.terms args) in
             let fq = Some?.v (FF.combine op qs) in
             let st2 = Some?.v (allocate st1 t) in
             lemma_prefix_append st1.terms t;
             lemma_append_last st1.terms t;
             lemma_prefix_trans st1.terms st2.terms final;
             FF.lemma_scoped_app f args;
             lemma_visit_args i rho project p st args st1 final;
             lemma_prefix_trans st.terms st1.terms st2.terms;
             lemma_prefix_index st2.terms final (L.length st1.terms);
             lemma_definition i rho project p st1.terms final f args op qs fq
           | None ->
             lemma_prefix_append st.terms t)
        | _ -> ()

and lemma_visit_args (i:interpretation value) (rho:env value) (project:int -> value -> int)
                     (p:pos) (st:encoding) (args:list expr) (st':encoding) (final:list expr)
  : Lemma (requires FF.ff_model i project /\ p >= 2 /\ D.scoped_args [] args /\
                    visit_args p st args == Some st' /\ prefix st'.terms final)
          (ensures prefix st.terms st'.terms /\
                   (eqs_ok i rho (valuation i rho project p final) p st.equations ==>
                    eqs_ok i rho (valuation i rho project p final) p st'.equations))
          (decreases args)
  = match args with
    | [] -> lemma_prefix_refl st.terms
    | a :: rest ->
      let st1 = Some?.v (visit_args p st rest) in
      FF.lemma_scoped_cons a rest;
      lemma_visit i rho project p st1 a st' final;
      lemma_prefix_trans st1.terms st'.terms final;
      lemma_visit_args i rho project p st rest st1 final;
      lemma_prefix_trans st.terms st1.terms st'.terms

let lemma_premise_equation (i:interpretation value) (rho:env value) (project:int -> value -> int)
                           (p:pos) (k:nat) (l a b:expr) (st:encoding) (positive:bool)
                           (st':encoding) (final:list expr)
  : Lemma (requires FF.ff_model i project /\ eq_sound i /\ p >= 2 /\
                    premise_parts p l == Some (positive, a, b) /\
                    premise_equation p k l a b st positive == Some st' /\ prefix st'.terms final)
          (ensures prefix st.terms st'.terms /\
                   (eqs_ok i rho (valuation i rho project p final) p st.equations ==>
                    eqs_ok i rho (valuation i rho project p final) p st'.equations))
  = if positive then (
      lemma_prefix_refl st.terms;
      let qa = Some?.v (term_poly p st.terms a) in
      let qb = Some?.v (term_poly p st.terms b) in
      assert (PT.is_not l == None);
      lemma_premise i rho project p st.terms final l a b qa qb;
      lemma_eq_ok_index i rho (valuation i rho project p final) p
        (FF.padd qa (FF.pscale (-1) qb)) 0 k l)
    else lemma_prefix_append st.terms l

let rec lemma_bind (i:interpretation value) (rho:env value) (project:int -> value -> int)
                   (p:pos) (k:nat) (st:encoding) (ps:list expr) (st':encoding) (final:list expr)
  : Lemma (requires FF.ff_model i project /\ eq_sound i /\ p >= 2 /\
                    bind p k st ps == Some st' /\ prefix st'.terms final)
          (ensures prefix st.terms st'.terms /\
                   (eqs_ok i rho (valuation i rho project p final) p st.equations ==>
                    eqs_ok i rho (valuation i rho project p final) p st'.equations))
          (decreases ps)
  = match ps with
    | [] -> lemma_prefix_refl st.terms
    | l :: rest ->
      let (positive, a, b) = Some?.v (premise_parts p l) in
      let st1 = Some?.v (visit p st a) in
      let st2 = Some?.v (visit p st1 b) in
      let st3 = Some?.v (premise_equation p k l a b st2 positive) in
      lemma_bind i rho project p (k + 1) st3 rest st' final;
      lemma_prefix_trans st3.terms st'.terms final;
      lemma_premise_equation i rho project p k l a b st2 positive st3 final;
      lemma_prefix_trans st2.terms st3.terms final;
      lemma_visit i rho project p st1 b st2 final;
      lemma_prefix_trans st1.terms st2.terms final;
      lemma_visit i rho project p st a st1 final;
      lemma_prefix_trans st.terms st1.terms st2.terms;
      lemma_prefix_trans st.terms st2.terms st3.terms;
      lemma_prefix_trans st.terms st3.terms st'.terms

let tree_ok (i:interpretation value) (rho:env value) (v:nat -> int) (p:pos)
            (tree:index_tree equation) : prop =
  forall (j:nat) (e:equation). index_get tree j == Some e ==> eq_ok i rho v p e

let rec lemma_index_equations (i:interpretation value) (rho:env value) (v:nat -> int) (p:pos)
                              (tree:index_tree equation) (k:int) (es:list equation)
  : Lemma (requires tree_ok i rho v p tree /\ eqs_ok i rho v p es)
          (ensures tree_ok i rho v p (index_equations tree k es))
          (decreases es)
  = match es with
    | [] -> ()
    | e :: rest ->
      if k < 0 then ()
      else (
        let tree' = index_put tree k e in
        let aux (j:nat) : Lemma (index_get tree' j == (if j = k then Some e else index_get tree j)) =
          lemma_index_put tree k e j in
        FStar.Classical.forall_intro aux;
        lemma_index_equations i rho v p tree' (k - 1) rest)

(* ----------------------------------------------------------------- *)
(* Soundness of the replay                                             *)
(* ----------------------------------------------------------------- *)

let rec none_true (i:interpretation value) (rho:env value) (lits:list expr)
  : Tot prop (decreases lits) =
  match lits with
  | [] -> True
  | l :: rest -> ~(lit_true i rho l) /\ none_true i rho rest

let rec lemma_negated_in (i:interpretation value) (rho:env value) (l:expr) (lits:list expr)
  : Lemma (requires O.boolean_model i /\ not_sound i /\ get_sort l == bool_sort /\
                    none_true i rho lits /\ negated_in l lits)
          (ensures lit_true i rho l)
          (decreases lits)
  = match lits with
    | x :: rest ->
      if PT.is_not x = Some l then
        (match x with
         | App f [_] -> lemma_not_relates i rho f l)
      else lemma_negated_in i rho l rest

let rec lemma_clause_holds (i:interpretation value) (rho:env value) (lits:list expr)
  : Lemma (requires ~(clause_holds i rho lits)) (ensures none_true i rho lits) (decreases lits)
  = match lits with
    | [] -> ()
    | _ :: rest -> lemma_clause_holds i rho rest

#push-options "--fuel 2"
let lemma_clause_literals (i:interpretation value) (rho:env value) (e:expr)
  : Lemma (requires or_sound i /\ ~(lit_true i rho e))
          (ensures none_true i rho (clause_literals e))
  = match e with
    | App f args -> if C.canonical_or f then lemma_clause_holds i rho args else ()
    | _ -> ()
#pop-options

let node_ok (i:interpretation value) (rho:env value) (v:nat -> int) (p:pos)
            (lits:list expr) (q:FF.poly) : prop =
  none_true i rho lits ==> FF.peval v q % p == 0

let values_ok (i:interpretation value) (rho:env value) (v:nat -> int) (p:pos)
              (lits:list expr) (tree:index_tree FF.poly) : prop =
  forall (j:nat) (q:FF.poly). index_get tree j == Some q ==> node_ok i rho v p lits q

let lemma_record (i:interpretation value) (rho:env value) (v:nat -> int) (p:pos)
                 (lits:list expr) (r:replay) (cost:nat) (q:FF.poly) (used:index_tree bool)
  : Lemma (requires values_ok i rho v p lits r.values /\ node_ok i rho v p lits q)
          (ensures values_ok i rho v p lits (Some?.v (record p r cost q used)).values)
  = lemma_normalize v p q;
    let q' = normalize p q in
    let aux (j:nat) : Lemma (index_get (index_put r.values r.next q') j ==
                             (if j = r.next then Some q' else index_get r.values j)) =
      lemma_index_put r.values r.next q' j in
    FStar.Classical.forall_intro aux

let lemma_tree_get (i:interpretation value) (rho:env value) (v:nat -> int) (p:pos)
                   (tree:index_tree equation) (j:nat) (e:equation)
  : Lemma (requires tree_ok i rho v p tree /\ index_get tree j == Some e)
          (ensures eq_ok i rho v p e)
  = ()

let lemma_values_get (i:interpretation value) (rho:env value) (v:nat -> int) (p:pos)
                     (lits:list expr) (tree:index_tree FF.poly) (j:nat) (q:FF.poly)
  : Lemma (requires values_ok i rho v p lits tree /\ index_get tree j == Some q)
          (ensures node_ok i rho v p lits q)
  = ()

let lemma_step (i:interpretation value) (rho:env value) (v:nat -> int) (p:pos)
               (nvars:nat) (eqs:index_tree equation) (sup:index_tree bool)
               (lits:list expr) (r:replay) (n:pac_node) (r':replay)
  : Lemma (requires O.boolean_model i /\ not_sound i /\ tree_ok i rho v p eqs /\
                    values_ok i rho v p lits r.values /\ step p nvars eqs sup lits r n == Some r')
          (ensures values_ok i rho v p lits r'.values)
  = match n with
    | PacInput j ->
      (match index_get eqs j with
       | Some (q, Definition) ->
         lemma_tree_get i rho v p eqs j (q, Definition);
         lemma_record i rho v p lits r (size q) q r.used
       | Some (q, Premise k l) ->
         lemma_tree_get i rho v p eqs j (q, Premise k l);
         let aux () : Lemma (requires none_true i rho lits) (ensures FF.peval v q % p == 0) =
           lemma_negated_in i rho l lits in
         FStar.Classical.move_requires aux ();
         lemma_record i rho v p lits r (size q) q (index_put r.used k true))
    | PacAdd a b ->
      let qa = Some?.v (earlier r a) in
      let qb = Some?.v (earlier r b) in
      lemma_values_get i rho v p lits r.values a qa;
      lemma_values_get i rho v p lits r.values b qb;
      FF.lemma_padd v qa qb;
      let aux () : Lemma (requires none_true i rho lits) (ensures FF.peval v (FF.padd qa qb) % p == 0) =
        lemma_zero_sum p (FF.peval v qa) (FF.peval v qb) in
      FStar.Classical.move_requires aux ();
      lemma_record i rho v p lits r (size qa + size qb) (FF.padd qa qb) r.used
    | PacMul s c fs ->
      let q = Some?.v (earlier r s) in
      let (_, k) = Some?.v (FF.numeral c) in
      let vs = Some?.v (variables nvars 0 fs) in
      lemma_values_get i rho v p lits r.values s q;
      lemma_scale_mono v vs k q;
      let aux () : Lemma (requires none_true i rho lits)
                         (ensures FF.peval v (scale_mono vs k q) % p == 0) =
        lemma_zero_product p (k * FF.mval v vs) (FF.peval v q) in
      FStar.Classical.move_requires aux ();
      lemma_record i rho v p lits r (size q + L.length q * L.length vs) (scale_mono vs k q) r.used

let rec lemma_replay_nodes (i:interpretation value) (rho:env value) (v:nat -> int) (p:pos)
                           (nvars:nat) (eqs:index_tree equation) (sup:index_tree bool)
                           (lits:list expr) (r:replay) (ns:list pac_node) (r':replay)
  : Lemma (requires O.boolean_model i /\ not_sound i /\ tree_ok i rho v p eqs /\
                    values_ok i rho v p lits r.values /\
                    replay_nodes p nvars eqs sup lits r ns == Some r')
          (ensures values_ok i rho v p lits r'.values)
          (decreases ns)
  = match ns with
    | [] -> ()
    | n :: rest ->
      let r1 = Some?.v (step p nvars eqs sup lits r n) in
      lemma_step i rho v p nvars eqs sup lits r n r1;
      lemma_replay_nodes i rho v p nvars eqs sup lits r1 rest r'

let lemma_check (i:interpretation value) (rho:env value) (project:int -> value -> int)
                (c:certificate) (e:expr)
  : Lemma (requires FF.ff_model i project /\ O.boolean_model i /\ not_sound i /\ or_sound i /\
                    eq_sound i /\ check c e)
          (ensures lit_true i rho e)
  = let p : pos = Some?.v (FF.find_modulus_args c.pac_premises) in
    let st = Some?.v (bind p 0 empty_encoding c.pac_premises) in
    let sup = Some?.v (support_tree (L.length c.pac_premises) (-1) Empty c.pac_support) in
    let v = valuation i rho project p st.terms in
    let eqs = index_equations Empty (L.length st.equations - 1) st.equations in
    let lits = clause_literals e in
    let r = Some?.v (replay_nodes p (L.length st.terms) eqs sup lits initial_replay c.pac_nodes) in
    lemma_prefix_refl st.terms;
    lemma_bind i rho project p 0 empty_encoding c.pac_premises st st.terms;
    lemma_index_equations i rho v p Empty (L.length st.equations - 1) st.equations;
    lemma_replay_nodes i rho v p (L.length st.terms) eqs sup lits initial_replay c.pac_nodes r;
    lemma_values_get i rho v p lits r.values c.pac_root [([], 1)];
    lemma_peval_constant v 1;
    M.small_mod 1 p;
    let aux () : Lemma (requires ~(lit_true i rho e)) (ensures False) =
      lemma_clause_literals i rho e in
    FStar.Classical.move_requires aux ()

let lemma_check_sound (i:interpretation value) (rho:env value) (c:certificate) (e:expr)
  : Lemma (requires (exists (project:int -> value -> int). FF.ff_model i project) /\
                    O.boolean_model i /\ not_sound i /\ or_sound i /\ eq_sound i /\ check c e)
          (ensures lit_true i rho e)
  = let aux (project:int -> value -> int)
      : Lemma (requires FF.ff_model i project) (ensures lit_true i rho e)
      = lemma_check i rho project c e in
    FStar.Classical.exists_elim (lit_true i rho e)
      #(int -> value -> int) #(fun project -> FF.ff_model i project) () (fun project -> aux project)
