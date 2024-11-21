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



# Level three



# Level four



# Level five



# Level Six



# Level Seven



# Level Eight