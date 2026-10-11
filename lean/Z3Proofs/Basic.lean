namespace Z3Proofs

theorem add_zero_comm (n : Nat) : 0 + n = n + 0 := by
  simp

theorem equality_symmetry {A : Type} {a b : A} (h : a = b) : b = a :=
  Eq.symm h

theorem modus_ponens (p q : Prop) : p -> (p -> q) -> q :=
  fun hp hpq => hpq hp

theorem contradiction (p : Prop) (hp : p) (hnp : Not p) : False :=
  hnp hp

end Z3Proofs
