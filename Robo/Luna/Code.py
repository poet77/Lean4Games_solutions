# Level one

rfl

# Level two

obtain ⟨⟩ := n
simp
constructor
intro
simp
intro
apply Nat.succ_pos

# Level three

linarith

# Level four

linarith

# Level five

obtain h | h | h := lt_trichotomy x y
apply h₁
linarith
apply h₁
linarith
apply h₂
assumption
