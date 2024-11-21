# Level one

push_neg
apply Subset.antisymm
intro x h
constructor
rewrite [mem_compl_iff A x]
by_contra h1
have h2: x∈ A∪B := Or.inl h1
exact h h2
rewrite [mem_compl_iff B x]
by_contra h1
have h2: x∈ A∪B := Or.inr h1
exact h h2
intro x h
have h1: x∈ Aᶜ := h.left
have h2: x∈ Bᶜ :=h.right
rewrite [mem_compl_iff (A∪B) x]
rewrite [mem_compl_iff A x] at h1
rewrite [mem_compl_iff B x] at h2
by_contra h3
cases' h3 with h4 h5
exact h1 h4
exact h2 h5

# Level two

rewrite [← compl_compl (Aᶜ ∪ Bᶜ)]
apply Subset.antisymm
intro x h
rewrite [compl_union]
rewrite [compl_compl]
rewrite [compl_compl]
exact h
rewrite [compl_union]
intro x h
rewrite [compl_compl A] at h
rewrite [compl_compl B] at h
exact h

# Level three

apply Subset.antisymm
intro x h
have h1: x∈A := h.left
have h2: x∈B∪C := h.right
cases' h2 with h3 h4
have h5: x∈A∩B := And.intro h1 h3
exact Or.inl h5
have h6: x∈A∩C := And.intro h1 h4
exact Or.inr h6
intro x h
cases' h with h1 h2
have h2: x∈A := h1.left
have h3: x∈B := h1.right
have h4: x∈B∪C := Or.inl h3
exact And.intro h2 h4
have h3: x∈A := h2.left
have h4: x∈C := h2.right
have h5: x∈B∪C := Or.inr h4
exact And.intro h3 h5

# Level four

apply Subset.antisymm
intro x h
cases' h with h1 h2
have h2: x∈A∪B := Or.inl h1
have h3: x∈A∪C := Or.inl h1
exact And.intro h2 h3
have h3: x∈B := h2.left
have h4: x∈C := h2.right
have h5: x∈A∪B := Or.inr h3
have h6: x∈A∪C := Or.inr h4
exact And.intro h5 h6
intro x h
have h1: x∈ A∪B := h.left
have h2: x∈ A∪C := h.right
cases' h1 with h3 h4
exact Or.inl h3
cases' h2 with h5 h6
exact Or.inl h5
have h7: x∈B∩C := And.intro h4 h6
exact Or.inr h7

# Level five

intro x h
have hAC : x∈ A ∪ C
exact Or.inl h
have hBC: x∈ B∪C:= h1 hAC
cases' hBC with h3 h4
exact h3
have hac: x∈A∩C := And.intro h h4
have hbc: x∈B∩C:= h2 hac
exact hbc.left