theorem add_zero_example (n : Nat) : n + 0 = n := by
  rfl

-- #check Eq.refl


example (n : Nat) : n + 0 = n := by
  rfl

-- example (n : Nat) : 0 + n = n := by
--   rfl

-- #check 2 + 2 = 4


example (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [Nat.zero_add]


theorem zero_add_example (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [Nat.add_succ]
      rw [ih]

#print zero_add_example

#print Nat.add_succ
