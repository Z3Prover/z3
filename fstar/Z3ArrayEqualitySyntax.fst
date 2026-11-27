module Z3ArrayEqualitySyntax

open Z3AstTheory
open Z3ClauseSyntax
module A = Z3ArraySyntax
module LA = Z3LinearArithmeticAst
module AR = Z3ArithmeticSyntax

let int_array : sort = ArraySort [LA.int_s] LA.int_s

(* Only genuine, one-dimensional Int arrays have the infinite domain used
   below. In particular, do not generalize this test to scalar_sort. *)
let rec default_term (fuel:nat) (e:expr)
  : Tot (option expr) (decreases fuel) =
  if fuel = 0 || get_sort e <> int_array then None
  else match e with
  | App f [v] -> if A.const_array f v then Some v else None
  | App f [a; k; v] ->
    if A.store_app f a k v then default_term (fuel - 1) a else None
  | _ -> None

let unequal_defaults (e:expr) : bool =
  match A.equality_parts e with
  | Some (a, b) ->
    (match default_term 64 a, default_term 64 b with
     | Some x, Some y -> AR.equivalent (mk_eq_expr x y) false_expr
     | _, _ -> false)
  | None -> false

let rec lemma_default_sort (fuel:nat) (e d:expr)
  : Lemma (requires default_term fuel e == Some d)
          (ensures get_sort d == LA.int_s)
          (decreases fuel) =
  if fuel = 0 then ()
  else match e with
  | App _ [_] -> ()
  | App _ [a; _; _] -> lemma_default_sort (fuel - 1) a d
  | _ -> ()
