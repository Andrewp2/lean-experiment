lemma mul_comm (a b : Nat) : a * b = b * a := by
  induction a with
  | zero =>
    simp
  | succ a ih =>
    simp [Nat.mul_succ, ih, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
