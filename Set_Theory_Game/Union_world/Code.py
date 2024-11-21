# Level one

exact Or.inl h

# Level two

intro x
rewrite [mem_union x A B]
intro h
exact Or.inr h

# Level three

intro x h3
cases' h3 with h4 h5
have h6: x∈C :=h1 h4
exact h6
have h7: x∈C := h2 h5
exact h7

# Level four

intro x h
cases' h with h1 h2
exact Or.inr h1
exact Or.inl h2

# Level five

apply Subset.antisymm
intro x h
cases' h with h1 h2
exact Or.inr h1
exact Or.inl h2
intro x h
cases' h with h1 h2
exact Or.inr h1
exact Or.inl h2

# Level six

apply Subset.antisymm
intro x h
cases' h with h1 h2 
cases' h1 with h3 h4
exact Or.inl h3
have h5:x∈B ∪ C := Or.inl h4
exact Or.inr h5
have h3:x∈B ∪ C := Or.inr h2
exact Or.inr h3
intro x h
cases' h with h1 h2
have h3: x∈ A∪B := Or.inl h1
exact Or.inl h3
cases' h2 with h6 h7
have h8: x∈ A∪B := Or.inr h6
exact Or.inl h8
exact Or.inr h7

