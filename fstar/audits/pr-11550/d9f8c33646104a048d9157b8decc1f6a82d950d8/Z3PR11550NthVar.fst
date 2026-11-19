module Z3PR11550NthVar
open FStar.List.Tot

(* Abstract sequence terms. Nth b i is seq.nth_i with a sequence-valued result. *)
type term =
  | Var : nat -> term
  | Nth : term -> int -> term
  | Unit : term -> term
  | Concat : term -> term -> term
  | Empty : term

(* eq_solver::is_var on the modelled constructors; the PR removes the !is_nth_i conjunct. *)
let is_var_base (t:term) : bool =
  match t with Var _ -> true | _ -> false
let is_var_head (t:term) : bool =
  match t with Var _ | Nth _ _ -> true | _ -> false

(* O1: the PR changes is_var exactly on nth_i terms. *)
let o1 (t:term) : Lemma (is_var_head t = (is_var_base t || Nth? t)) = ()

(* Term-keyed valuation: each variable/nth term has a value (congruence closure assumption). *)
noeq type env = { var : nat -> list int; nth : term -> list int }

let rec ev (e:env) (t:term) : Tot (list int) (decreases t) =
  match t with
  | Var n -> e.var n
  | Nth _ _ -> e.nth t
  | Unit b -> [List.Tot.length (ev e b)]
  | Concat a b -> ev e a @ ev e b
  | Empty -> []

(* occurs: syntactic search descending through concat, unit and nth_i (as in eq_solver::occurs). *)
let rec occurs (x:term) (t:term) : Tot bool (decreases t) =
  if x = t then true
  else match t with
  | Concat a b -> occurs x a || occurs x b
  | Unit b -> occurs x b
  | Nth b _ -> occurs x b
  | _ -> false

let override (e:env) (x:term) (v:list int) : env =
  { var = (fun n -> if x = Var n then v else e.var n);
    nth = (fun t -> if x = t then v else e.nth t) }

(* O3: reduce_unit soundness: if x does not occur in t, overriding x leaves t's value unchanged. *)
let rec o3_indep (e:env) (x:term{is_var_head x}) (v:list int) (t:term)
  : Lemma (ensures not (occurs x t) ==> ev (override e x v) t == ev e t) (decreases t)
  = match t with
    | Concat a b -> o3_indep e x v a; o3_indep e x v b
    | Unit b -> o3_indep e x v b
    | Nth b _ -> o3_indep e x v b
    | _ -> ()

let o3 (e:env) (x:term{is_var_head x}) (t:term)
  : Lemma (requires not (occurs x t))
          (ensures ev (override e x (ev e t)) x == ev (override e x (ev e t)) t)
  = o3_indep e x (ev e t) t

(* O2: branch_unit_variable: X = units and |X| = k imply X = first k of units. *)
let rec split_full (us:list int) : Lemma (fst (splitAt (length us) us) == us) =
  match us with [] -> () | _::t -> split_full t

let o2 (x us:list int) (k:nat)
  : Lemma (requires x == us /\ length x == k)
          (ensures x == fst (splitAt k us))
  = split_full us
