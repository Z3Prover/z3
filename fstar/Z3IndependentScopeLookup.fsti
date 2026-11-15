module Z3IndependentScopeLookup

module A = Z3AstTheory
module L = FStar.List.Tot

val matches (scope:list A.sort) (n:nat) (s:A.sort)
  : result:bool{result == (n < L.length scope && L.index scope n = s)}
