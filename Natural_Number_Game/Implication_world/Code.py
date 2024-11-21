# Level one

exact h1

# Level two

repeat rw [zero_add] at h
exact h

# Level three

apply h2 at h1
exact h1

# Level four

rw [four_eq_succ_three] at h
rw [← succ_eq_add_one] at h
apply succ_inj at h
exact h

# Level five

apply succ_inj
rw [succ_eq_add_one]
rw [succ_eq_add_one]
rw [four_eq_succ_three] at h
repeat rw [← succ_eq_add_one]
rw [← succ_eq_add_one] at h
exact h

# Level six

intro h
exact h

# Level seven

intro h
repeat rw [← succ_eq_add_one] at h
apply succ_inj
exact h

# Level eight

apply h2 at h1
exact h1

# Level nine

intro h
rw [one_eq_succ_zero] at h
apply zero_ne_succ at h
exact h

# Level ten

symm
intro h
rw [one_eq_succ_zero] at h
apply zero_ne_succ at h
exact h


# Level eleven

intro h
rw [succ_add] at h
apply succ_inj at h
rw [succ_add] at h
apply succ_inj at h
rw [zero_add] at h
apply succ_inj at h
apply succ_inj at h
apply zero_ne_succ at h
exact h
