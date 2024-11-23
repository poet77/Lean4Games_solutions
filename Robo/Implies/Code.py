# Level one

intro
constructor
assumption
assumption

# Level two

revert hA
assumption


# Level three

apply hAB at h
assumption

# Level four

intro
apply f at a
apply g at a
assumption

# Level five

intro
apply f at a
apply i at a
apply l at a
apply p at a
assumption

# Level six

constructor
assumption
assumption

# Level seven

symm at h
assumption

# Level eight

rw [h₁]
rw [← h₂]
assumption

# Level nine

trans A
symm
assumption
trans D
assumption
symm
assumption

# Level ten

intro
apply (h.mp) at a
apply g at a
assumption

# Level eleven

intro
obtain ⟨mp, mpr⟩ := a
assumption

# Level twelve

by_cases h : A
right
assumption

left
assumption

# Level 13

rw [not_not]
rw [not_not]

# Level 14

constructor
intro h
by_cases A
apply h at h_1
right
assumption
left
assumption
intro h1
intro ha
by_cases A
obtain h1 | h1 :=  h1
contradiction
assumption
contradiction