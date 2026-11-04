module Z3DemodNonGround
(* Model of demodulator_simplifier::mk_instance_proof under an outer quantifier.
   Terms use de Bruijn variables; binders inside terms are not modelled. *)
type term =
  | Var : nat -> term
  | App : nat -> list term -> term

type env = nat -> int
type interp = nat -> list int -> int

let rec eval (i:interp) (r:env) (t:term) : Tot int (decreases t) =
  match t with
  | Var k -> r k
  | App f args -> i f (eval_list i r args)
and eval_list (i:interp) (r:env) (l:list term) : Tot (list int) (decreases l) =
  match l with
  | [] -> []
  | x :: xs -> eval i r x :: eval_list i r xs

(* bindings: demodulator variable k -> possibly non-ground term of the outer context *)
let rec subst (b:nat -> term) (t:term) : Tot term (decreases t) =
  match t with
  | Var k -> b k
  | App f args -> App f (subst_list b args)
and subst_list (b:nat -> term) (l:list term) : Tot (list term) (decreases l) =
  match l with
  | [] -> []
  | x :: xs -> subst b x :: subst_list b xs

(* O1: substitution lemma; non-ground bindings are evaluated in the outer env r *)
let rec subst_eval (i:interp) (r:env) (b:nat -> term) (t:term)
  : Lemma (ensures eval i r (subst b t) == eval i (fun k -> eval i r (b k)) t)
          (decreases t) =
  match t with
  | Var _ -> ()
  | App f args -> subst_list_eval i r b args
and subst_list_eval (i:interp) (r:env) (b:nat -> term) (l:list term)
  : Lemma (ensures eval_list i r (subst_list b l) == eval_list i (fun k -> eval i r (b k)) l)
          (decreases l) =
  match l with
  | [] -> ()
  | x :: xs -> subst_eval i r b x; subst_list_eval i r b xs

(* O2: instance of a universal equation holds under every outer env *)
let instance_sound (i:interp) (l rhs:term) (r:env)
  (b:nat -> term)
  (h: (e:env -> Lemma (eval i e l == eval i e rhs)))
  : Lemma (eval i r (subst b l) == eval i r (subst b rhs)) =
  subst_eval i r b l; subst_eval i r b rhs;
  h (fun k -> eval i r (b k))

(* O3: exact match binds each variable to itself; qe[s] is then qe itself *)
let id_b : nat -> term = fun k -> Var k

let rec subst_id (t:term) : Lemma (ensures subst id_b t == t) (decreases t) =
  match t with
  | Var _ -> ()
  | App f args -> subst_id_list args; ()
and subst_id_list (l:list term) : Lemma (ensures subst_list id_b l == l) (decreases l) =
  match l with
  | [] -> ()
  | x :: xs -> subst_id x; subst_id_list xs
