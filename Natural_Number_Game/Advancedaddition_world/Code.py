# Level one

intro h
induction n with t nt
repeat rw [add_zero] at h
repeat rw [add_zero] at h
exact h
repeat rw [add_succ] at h
apply succ_inj at h
apply nt at h
exact h

# Level two

intro h
rw [add_comm n a] at h
rw [add_comm n b] at h
apply add_right_cancel at h
exact h

# Level three

induction y with k ky
intro h
rw [add_zero] at h
exact h

intro h
rw [add_succ] at h
apply succ_inj at h
apply ky at h
exact h

# Level four

intro h
rw [add_comm] at h
apply add_left_eq_self at h
exact h

# Level five

cases b with d
intro h
rw [add_zero] at h
exact h

intro h1
rw [add_succ] at h1
cases h1

# Level six

intro h
rw [add_comm a b] at h
apply add_right_eq_zero at h
exact h

