lemma bool_or (p q : Bool) : p || q = true := by
  cases p <;> cases q <;> decide
