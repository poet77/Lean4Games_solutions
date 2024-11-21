# Level one

have so : S ∨ O  :=or_inl s
exact so

# Level two

have ks: K ∨ S := or_inr s
exact ks

# Level three

have b : B := or_elim h3 h1 h2
exact b

# Level four

have oc := or_elim h or_inr or_inl
exact oc

# Level five

have h3 : C → J ∨ R :=λ hC ↦ or_inl (h1 hC)
have h4 : R → J ∨ R :=λ hR ↦ or_inr hR
exact or_elim h2 h3 h4

# Level six

have fg : G → (G ∨ H) ∧ (G ∨ U) := λg ↦ ⟨or_inl g, or_inl g⟩
have fhu : H ∧ U → (G ∨ H) ∧ (G ∨ U) :=    λhu ↦ ⟨or_inr hu.left, or_inr hu.right⟩
exact or_elim h fg fhu

# Level seven

have hvu := h.right
have ffh : H → (G ∧ H) ∨ (G ∧ U) :=    λx ↦ or_inl ⟨h.left, x⟩
have ffu : U → (G ∧ H) ∨ (G ∧ U) := λx ↦ or_inr ⟨h.left, x⟩
exact or_elim hvu ffh ffu

# Level eight

have ip : I → I ∨ P := λx ↦ or_inl x
have kip : K → I ∨ P := λt ↦ or_inr (h t)
exact λki ↦ or_elim ki kip ip