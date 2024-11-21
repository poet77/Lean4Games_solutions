# Level one

rfl

# Level two

rw [h]
rfl

# Level three

rw [two_eq_succ_one]
rw [one_eq_succ_zero]
rfl

# Level four

rw [two_eq_succ_one]
rw [← one_eq_succ_zero]
rfl

# Level five

rw [add_zero]
rw [add_zero]
rfl

# Level six

rw [add_zero c]
rw [add_zero b]
rfl

# Level seven

rw [one_eq_succ_zero]
rw [add_succ]
rw [add_zero]
rfl

# Level eight

nth_rewrite 2 [two_eq_succ_one]
rw [add_succ]
rw [four_eq_succ_three]
rw [three_eq_succ_two]
rw [← succ_eq_add_one]
rfl