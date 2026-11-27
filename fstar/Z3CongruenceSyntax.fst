module Z3CongruenceSyntax

open Z3AstTheory
open Z3UnifiedProofSyntax

let step (r:relation) (a b:expr) (facts:list judgment) : bool =
  a = b || (match a, b with
   | App f xs, App g ys -> f = g && all_edges r facts && fast_arguments_match r xs ys facts
   | _, _ -> false)
