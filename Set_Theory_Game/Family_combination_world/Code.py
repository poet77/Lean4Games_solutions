# Level one

ext x
apply Iff.intro
intro h1
rw [mem_sInter]
intro t h2
rewrite [mem_setOf] at h2
rewrite [mem_compl_iff] at h1
by_contra h3
rewrite [mem_sUnion] at h1
push_neg at h1
have h4 := h1 tᶜ h2
rewrite [mem_compl_iff] at h4
push_neg at h4
exact h3 h4
intro h1
rewrite [mem_sInter] at h1
rewrite [mem_compl_iff]
rewrite [mem_sUnion]
push_neg
intro t h2
have h3 := h1 tᶜ
have h3a : tᶜ ∈ {A | Aᶜ ∈ F}
rewrite [mem_setOf]
rewrite [compl_compl]
exact h2
have h4 := h3 h3a
rewrite [mem_compl_iff] at h4
exact h4

# Level two

ext x
apply Iff.intro
intro h1
rewrite [mem_compl_iff] at h1
rewrite [mem_sInter] at h1
push_neg at h1
obtain ⟨t, ht⟩ := h1
use tᶜ
rewrite [mem_setOf, compl_compl, mem_compl_iff]
exact ht
intro h1
rewrite [mem_compl_iff, mem_sInter]
push_neg
rewrite [mem_sUnion] at h1
obtain ⟨u, hu⟩ := h1
use uᶜ
apply And.intro
rewrite [mem_setOf] at hu
exact hu.left
rewrite [mem_compl_iff]
push_neg
exact hu.right

# Level three

obtain ⟨s, h3⟩ := h2
have h4 := h1 s h3.left
obtain ⟨t, h5⟩ := h4
have h6 : t ⊆ s := h3.right t h5.left
have h7 : s = t := Subset.antisymm h5.right h6
use s
apply And.intro
exact h3.left
rewrite [h7]
exact h5.left

# Level four

intro x h2
rewrite [mem_inter_iff] at h2
have h2l := h2.left
have h2r := h2.right
rewrite [mem_sUnion] at h2l
obtain ⟨t, ht⟩ := h2l
have h3 := h1 t ht.left
obtain ⟨u, hu⟩ := h3
rewrite [mem_sInter] at h2r
have h3 := h2r u hu.left
rewrite [mem_sUnion]
use t ∩ u
apply And.intro hu.right
rewrite [mem_inter_iff]
exact And.intro ht.right h3

# Level five

intro x h1
rewrite [mem_inter_iff] at h1
have h1l := h1.left
rewrite [mem_sUnion] at h1l
obtain ⟨t, ht⟩ := h1l
rewrite [mem_sUnion]
use t
apply And.intro
rewrite [mem_inter_iff]
apply And.intro
exact ht.left
rewrite [mem_compl_iff]
by_contra h2
have h1r := h1.right
rewrite [mem_compl_iff, mem_sUnion] at h1r
push_neg at h1r
have hnt := h1r t h2
exact hnt ht.right
exact ht.right

# Level Six

intro x h2
have h2l := h2.left
have h2r := h2.right
rewrite [mem_sUnion] at h2l
obtain ⟨t, ht⟩ := h2l
use t
apply And.intro
apply And.intro
exact ht.left
by_contra h3
have h4 : x ∈ ⋃₀ (F ∩ Gᶜ)
use t
apply And.intro
apply And.intro
exact ht.left
rewrite [mem_compl_iff]
exact h3
exact ht.right
have h5 := h1 h4
have h5r := h5.right
rewrite [mem_compl_iff] at h5r
exact h5r h2r
exact ht.right

# Level Seven

intro x h1
have h1l := h1.left
have h1r := h1.right
rewrite [mem_sUnion] at h1l
obtain ⟨u, hu⟩ := h1l
rewrite [mem_compl_iff, mem_sInter] at h1r
push_neg at h1r
obtain ⟨v, hv⟩ := h1r
rewrite [mem_sUnion]
use u ∩ vᶜ
apply And.intro
rewrite [mem_setOf]
use u
apply And.intro
exact hu.left
use v
apply And.intro
exact hv.left
rfl
rewrite [mem_inter_iff, mem_compl_iff]
exact And.intro hu.right hv.right

# Level Eight

have h2 := h1 {s | ∃ x ∈ A, s = {x}}
have h3 : ⋃₀ {s | ∃ x ∈ A, s = {x}} = A
ext x
apply Iff.intro
intro h3
obtain ⟨t, ht⟩ := h3
rewrite [mem_setOf] at ht
obtain ⟨y, hy⟩ := ht.left
rewrite [hy.right] at ht
rewrite [mem_singleton_iff] at ht
rewrite [ht.right]
exact hy.left
intro h3
use {x}
apply And.intro
rewrite [mem_setOf]
use x
rewrite [mem_singleton_iff]
rfl
have h4 := h2 h3
rewrite [mem_setOf] at h4
obtain ⟨y, hy⟩ := h4
use y
exact hy.right