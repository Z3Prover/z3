module Z3ExprScope

open Z3AstTheory
open FStar.List.Tot
module L = FStar.List.Tot

let rec scoped (scope:list sort) (e:expr) : Tot bool (decreases e) =
  match e with
  | Var n s -> n < L.length scope && L.index scope n = s
  | App f args -> sorts_match args f.domain && scoped_args scope args
  | Quantifier k bs s b ->
    s = quant_sort k bs (get_sort b) &&
    (k = Lambda_k || get_sort b = bool_sort) &&
    scoped (L.rev bs @ scope) b

and scoped_args (scope:list sort) (args:list expr) : Tot bool (decreases args) =
  match args with
  | [] -> true
  | a :: rest -> scoped scope a && scoped_args scope rest

let rec lemma_scoped_reverse_acc (scope:list sort) (args acc:list expr)
  : Lemma (requires scoped_args scope args /\ scoped_args scope acc)
          (ensures scoped_args scope (L.rev_acc args acc))
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest -> lemma_scoped_reverse_acc scope rest (a :: acc)
