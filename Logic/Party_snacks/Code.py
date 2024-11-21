# Level one

exact bakery_service p

# Level two

exact λ(h: C) ↦ h

# Level three

exact λ(h : I ∧ S) ↦ and_intro (and_right h) (and_left h)

# Level four

exact h2 ∘ h1

# Level five

have pqt := imp_trans h1 h3
have tu := imp_trans pqt h5
exact tu p

# Level six

exact λc d ↦ h (and_intro c d)

# Level seven

exact λ(cd:C ∧ D) ↦ h cd.left cd.right

# Level eight

exact λ(s: S)  ↦ and_intro (h.left s) (h.right s)

# Level nine

have sr := λ(r: R)(t : S) ↦ r
have sr2 := λ (r: R)(t: ¬S) ↦ r
exact λ(r:R) ↦ and_intro (sr r) (sr2 r)