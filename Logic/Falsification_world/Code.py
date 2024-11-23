# Level one

exact identity

# Level two

exact imp_trans h false_elim

# Level three

exact λ(np : ¬P) ↦ np p

# Level four

exact λ(h : L ∧ ¬L) ↦ h.right h.left

# Level five

exact h2 ∘ h1

# Level six

exact λ(a : A) ↦ h a a

# Level seven

exact λ(c : C) ↦ h (λ(_ : B) ↦ c)

# Level eight

exact  λ(sc : ¬S ∧ C) ↦ sc.left s

# Level nine

exact λ(pa : P ∧ A) ↦ h pa.left pa.right

# Level ten

exact λ(p: P)(a : A) ↦ h (and_intro p a)

# Level eleven

exact λa ↦ h λna ↦ na a

# Level twelve

exact λnb ↦ h (λb ↦ false_elim (nb b))