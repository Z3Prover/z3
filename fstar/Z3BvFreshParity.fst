module Z3BvFreshParity

open Z3AstTheory
module B = Z3BvSyntax
module Old = Z3BvLemma
module W = Z3BvWord

let word_parts (e:expr) : Lemma (B.word_parts e == Old.word_parts e) =
  match e with
  | App f args -> (match f.int_params with [_] -> () | _ -> ())
  | _ -> ()

let projection (width:pos) (source:expr) (bit:nat)
  : Lemma (B.projection width source bit == W.projection width source bit) = ()
