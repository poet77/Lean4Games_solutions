# Level one

have sj := iff_intro hsj hjs
exact sj

# Level two

have bp:= iff_mp h
have pb:= iff_mpr h
have goal:= and_intro bp pb
exact goal

# Level three

have rq:= h1.mp
have pr:= imp_trans h2 rq
exact pr

# Level four

have rp:= h1.mpr
have rq:= imp_trans rp h2
exact rq

# Level five

rw [h1]
exact h2

# Level six

rw [or_assoc]
rw [and_assoc]
exact h

# Level seven

exact ⟨
    λ⟨pr,rp⟩ q ↦ ⟨λp ↦ (pr ⟨p,q⟩).left, λr ↦ (rp ⟨r,q⟩).left⟩,
    λqpr ↦ ⟨λ⟨p,q⟩ ↦ ⟨(qpr q).mp p, q⟩, λ⟨r,q⟩ ↦ ⟨(qpr q).mpr r, q⟩⟩
  ⟩