module Z3PR11571ScopedModel

open FStar.List.Tot
module L = FStar.List.Tot

(* Self-contained abstraction of Z3Definitions.scoped / scoped_args: the sort
   and sorts_match/quant_sort side conditions are abstracted by an opaque
   predicate `ok`, but the structural recursion over App arguments and
   Quantifier bodies (the only part the PR's helper lemmas use) is kept. *)

type quantifier_kind = | Forall_k | Exists_k | Lambda_k

type expr =
  | Var : idx:nat -> s:nat -> expr
  | App : decl:nat -> args:list expr -> expr
  | Quantifier : qk:quantifier_kind -> bound_sorts:list nat -> qsort:nat -> body:expr -> expr

noeq type side = {
  app_ok : nat -> list expr -> bool;
  quant_ok : quantifier_kind -> list nat -> nat -> expr -> bool;
}

let rec scoped (c:side) (scope:list nat) (e:expr) : Tot bool (decreases e) =
  match e with
  | Var n s -> n < L.length scope && L.index scope n = s
  | App f args -> c.app_ok f args && scoped_args c scope args
  | Quantifier k bs s b -> c.quant_ok k bs s b && scoped c (L.rev bs @ scope) b

and scoped_args (c:side) (scope:list nat) (args:list expr) : Tot bool (decreases args) =
  match args with
  | [] -> true
  | a :: rest -> scoped c scope a && scoped_args c scope rest

let lemma_scoped_binary (c:side) (scope:list nat) (f:nat) (x y:expr)
  : Lemma (requires scoped c scope (App f [x; y]))
          (ensures scoped c scope x /\ scoped c scope y) =
  assert (scoped_args c scope [x; y]);
  assert (scoped_args c scope [y])

let lemma_scoped_ternary (sc:side) (scope:list nat) (f:nat) (c x y:expr)
  : Lemma (requires scoped sc scope (App f [c; x; y]))
          (ensures scoped sc scope c /\ scoped sc scope x /\ scoped sc scope y) =
  assert (scoped_args sc scope [c; x; y]);
  assert (scoped_args sc scope [x; y]);
  assert (scoped_args sc scope [y])

let lemma_scoped_quantifier_pair (c:side) (f:nat) (k k':quantifier_kind) (bs bs':list nat) (t t':nat) (a b:expr)
  : Lemma (requires scoped c [] (App f [Quantifier k bs t a; Quantifier k' bs' t' b]))
          (ensures scoped c [] (Quantifier k bs t a) /\ scoped c [] (Quantifier k' bs' t' b) /\
                   scoped c (L.rev bs @ []) a /\ scoped c (L.rev bs' @ []) b) =
  assert (scoped_args c [] [Quantifier k bs t a; Quantifier k' bs' t' b]);
  assert (scoped_args c [] [Quantifier k' bs' t' b])
