# Level one

exact h

# Level two

exact h1 h2

# Level three

have h4 : x∈ B := h1 h3
exact h2 h4

# Level four

intro h3
have h4 : x ∈ B := h1 h3
exact h2 h4

# Level five

intro x
intro h1
exact h1

# Level six

intro x
intro h3
have h4: x∈ B := h1 h3
have h5: x ∈ C := h2 h4
exact h5

