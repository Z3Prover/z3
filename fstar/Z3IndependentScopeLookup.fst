module Z3IndependentScopeLookup

module A = Z3AstTheory
module L = FStar.List.Tot

let matches (scope:list A.sort) (n:nat) (s:A.sort)
  : result:bool{result == (n < L.length scope && L.index scope n = s)} =
  if n = 0 then
    match scope with
    | [] -> false
    | head :: _ -> head = s
  else n < L.length scope && L.index scope n = s
