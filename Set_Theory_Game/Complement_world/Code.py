# Level one

by_contra h3
have h4: x∈ B:=h3 h1
exact h2 h4

# Level two

rfl

# Level three

intro  x h2
rewrite [mem_compl_iff A x]
by_contra h3
have h4:x∈ B:=h1 h3
exact h2 h4

# Level four

apply Subset.antisymm
intro x h1
have h2: ¬x ∈Aᶜ :=h1
have h3: ¬x ∉A :=h2
push_neg at h3
exact h3
intro y h1
by_contra h4
have h5: ¬y ∉Aᶜ:=h4
push_neg at h5 
have h6: y∉A:=h5
have h7: ¬y ∈A:=h6
exact h7 h1

# Level five

apply Iff.intro
intro x
apply compl_subset_compl_of_subset x
intro h
have h1:Aᶜᶜ ⊆ Bᶜᶜ :=compl_subset_compl_of_subset h
rewrite [compl_compl A] at h1
rewrite [compl_compl B] at h1
exact h1

