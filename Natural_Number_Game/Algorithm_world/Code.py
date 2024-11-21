# Level one

rw [← add_assoc]
rw [add_comm a b]
rw [← add_assoc]
rfl

# Level two

repeat rw [add_assoc]
rw [add_left_comm b c]
rw [add_comm b d]
rfl

# Level three

simp only [add_assoc, add_left_comm, add_comm]

# Level four

simp only [add_assoc, add_left_comm, add_comm]

# Level five

rw [← pred_succ a]
rw [← pred_succ b]
rw [h]
rfl

# Level Six

intro h
rw [← is_zero_succ a]
trivial

# Level seven

contrapose! h
apply succ_inj at h
exact h

# Level eight

decide

# Level nine

decide