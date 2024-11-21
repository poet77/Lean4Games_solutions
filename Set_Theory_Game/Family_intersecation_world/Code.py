# Level one

intro x h
rewrite[mem_sInter] at h
have hA := h A
exact hA h1

# Level two

intro x h
rewrite [mem_sInter]
rewrite [mem_sInter] at h
intro t
intro h2
have h3: t∈G := h1 h2
exact h t h3

# Level three

apply Subset.antisymm
intro x h
rewrite [mem_sInter]
intro t
rewrite [mem_pair t A B]
cases' h with h1 h2
intro h3
cases' h3 with h4 h5
rw [h4]
exact h1
rw [h5]
exact h2
intro x h
rewrite [mem_sInter] at h
constructor
have h1 :A ∈ {A, B}
have h2: A⊆A := Subset.refl A
have h3: A=A
apply Subset.antisymm h2
exact h2
exact Or.inl h3
exact h A h1
have h1: B∈ {A,B}
have h2: B⊆B := Subset.refl B
have h3: B=B
apply Subset.antisymm h2
exact h2
exact Or.inr h3
exact h B h1

# Level four

apply Subset.antisymm
intro x h
rewrite [mem_sInter] at h
constructor
rw [mem_sInter]
intro t
intro h1
have hFG : t∈ F ∪ G:=Or.inl h1
exact h t hFG
rw [mem_sInter]
intro t h1
have hFG : t ∈ F ∪ G:= Or.inr h1
exact h t hFG
intro x h
rw [mem_sInter]
cases' h
rw [mem_sInter] at left
intro t
rw [mem_sInter] at right
intro h1
cases' h1 with h2 h3
exact left t h2
exact right t h3

# Level five

constructor
intro a
intro t
intro s
have h1: ⋂₀F ⊆ t
intro x
intro h1
rw [mem_sInter] at h1
exact h1 t s
exact Subset.trans a h1
intro x t
intro h1
rw [mem_sInter]
intro t_1
intro h2
have h3: A⊆t_1
exact x t_1 h2
exact h3 h1

# Level Six

intro x
intro h2
by_cases h3:x∈A
exact Or.inl h3
apply Or.inr
rw [mem_sInter]
intro S
rw [mem_sInter] at h2
intro h4
have h5 := h2 (A∪S)
have h6 := h1 S h4
have h7 := h5 h6
cases' h7 with h8 h9
by_contra h10
exact h3 h8
exact h9