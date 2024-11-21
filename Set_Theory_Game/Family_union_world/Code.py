# Level one

have h : A ⊆ A := Subset.refl A
exact Exists.intro A h

# Level two

intro x
intro h2
rw [mem_sUnion]
apply Exists.intro A
exact And.intro h1 h2

# Level three

intro x
intro h2
rw [mem_sUnion]
rw [mem_sUnion] at h2
obtain ⟨B,hB⟩ := h2
use B
have h2 := h1 hB.left
have h3 := And.intro h2 hB.right
exact h3

# Level four

apply Subset.antisymm
intro x h
rewrite [mem_sUnion]
cases' h with h1 h2
apply Exists.intro A
rw [mem_pair]
have h2: A = A := rfl
exact And.intro (Or.inl h2) h1
apply Exists.intro B
rw [mem_pair]
have h3: B=B := rfl
exact And.intro (Or.inr h3) h2
intro x h
rewrite [mem_sUnion] at h
obtain ⟨C,hC⟩ := h
cases' hC
rw [mem_pair] at left
cases' left with h1 h2
rw [h1] at right
left
exact right
rw [h2] at right
right
exact right

# Level five

apply Subset.antisymm
intro x h
rw [mem_sUnion] at h
obtain ⟨W, hW⟩ := h
cases' hW
cases' left with h1 h2
left
rw [mem_sUnion]
apply Exists.intro W
exact And.intro h1 right
right
rw [mem_sUnion]
apply Exists.intro W
exact And.intro h2 right
intro x h
cases' h with h1 h2
rw [mem_sUnion] at h1
obtain ⟨W,hW⟩  := h1
cases' hW with h1 h2
rw [mem_sUnion]
apply Exists.intro W
have h3: W∈ F∪G := Or.inl h1
exact And.intro h3 h2
rw [mem_sUnion] at h2
rw [mem_sUnion]
obtain ⟨W,hW⟩ := h2
apply Exists.intro W
cases' hW with h1 h2
have h3: W∈ F∪ G := Or.inr h1
exact And.intro h3 h2

# Level six

constructor
intro a
intro t
intro s
have h1: t ⊆ ⋃₀F
intro x
intro h2
rw [mem_sUnion]
apply Exists.intro t
exact And.intro s h2
apply Subset.trans h1 a
intro x t
intro h1
rw [mem_sUnion] at h1
obtain ⟨W, hW⟩ := h1
cases' hW
have h3: W⊆A
exact x W left
exact h3 right

# Level seven

ext x
apply Iff.intro
intro h1
rewrite [mem_inter_iff] at h1
have h2 : x ∈ ⋃₀ F := h1.right
rewrite [mem_sUnion] at h2
obtain ⟨t, ht⟩ := h2
rewrite [mem_sUnion]
use A ∩ t
apply And.intro
rewrite [mem_setOf]
use t
apply And.intro
exact ht.left
rfl
exact And.intro h1.left ht.right
intro h1
obtain ⟨t, ht⟩ := h1
have htl := ht.left
rewrite [mem_setOf] at htl
obtain ⟨u, hu⟩ := htl
rewrite [hu.right, mem_inter_iff] at ht
rewrite [mem_inter_iff]
apply And.intro
exact ht.right.left
rewrite [mem_sUnion]
use u
exact And.intro hu.left ht.right.right