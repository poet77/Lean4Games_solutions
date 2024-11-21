# Level one

have h1:x∈A:=h.left
exact h1

# Level two

rewrite [mem_inter_iff] at h
have h1:x∈B :=h.right
exact h1

# Level three

intro x h
rewrite [mem_inter_iff] at h
have h1: x∈A :=h.left
exact h1

# Level four

exact And.intro h1 h2

# Level five

intro x h3
constructor
exact h1 h3
exact h2 h3

# Level six

intro x h
constructor
rewrite [mem_inter_iff] at h
have h1: x∈B :=h.right
exact h1
have h2: x∈A :=h.left
exact h2

# Level seven

apply Subset.antisymm
apply inter_subset_swap
apply inter_subset_swap

# Level eight

ext x
apply Iff.intro
intro h1
have h2: x∈A ∩ B := h1.left
have h3: x∈C :=h1.right
have h4: x∈A := h2.left
have h5: x∈B := h2.right
have h6: x∈B ∩ C := And.intro h5 h3
exact And.intro h4 h6
intro h1
have h2: x∈A := h1.left
have h3: x∈B ∩ C := h1.right
have h4: x∈B := h3.left
have h5: x∈C := h3.right
have h6: x∈A ∩ B := And.intro h2 h4
exact And.intro h6 h5