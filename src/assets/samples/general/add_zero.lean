theorem add_zero (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [Nat.add_succ, ih]
