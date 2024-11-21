# Level one

rw [one_eq_succ_zero]
rw [mul_succ]
rw [mul_zero]
rw [zero_add]
rfl

# Level two

induction m with k km
rw [mul_zero]
rfl
rw [mul_succ]
rw [km]
rw [add_zero]
rfl

# Level three

induction b with k kb
rw [mul_zero]
rw [mul_zero]
rw [add_zero]
rfl
rw [mul_succ]
rw [mul_succ]
rw [kb]
rw [add_assoc]
rw [add_assoc]
rw [succ_eq_add_one]
rw [succ_eq_add_one]
rw [←add_assoc a k 1]
rw [←add_assoc k a 1]
rw [add_comm k a]
rfl

# Level four

induction b with k kh
rw [zero_mul]
rw [mul_zero]
rfl

rw [mul_succ]
rw [succ_mul]
rw [kh]
rfl

# Level five

induction m with k km
rw [mul_zero]
rfl

rw [mul_succ]
rw [km]
rw [succ_eq_add_one]
rfl

# Level six

induction m with k km
rw [mul_zero]
rw [add_zero]
rfl

rw [add_succ]
rw [mul_succ]
rw [km]
rw [succ_eq_add_one]
rw [succ_eq_add_one]
rw [add_right_comm k 1 k]
rw [two_eq_succ_one]
rw [succ_eq_add_one 1]
rw [← add_assoc]
rfl

# Level seven

induction c with k kc
rw [add_zero]
rw [mul_zero]
rw [add_zero]
rfl

rw [mul_succ]
rw [add_succ]
rw [mul_succ]
rw [kc]
rw [add_assoc]
rfl

# Level eight

induction c with k km
rw [mul_zero]
rw [mul_zero]
rw [mul_zero]
rw [add_zero]
rfl

rw [mul_succ]
rw [mul_succ]
rw [mul_succ]
rw [km]
rw [add_assoc]
rw [add_right_comm]
rw [add_assoc]
rw [add_comm a b]
rw [add_assoc (b * k) b a]
rfl

# Level nine

induction c with k km
rw [mul_zero]
rw [mul_zero]
rw [mul_zero]
rfl

rw [mul_succ]
rw [mul_succ]
rw [mul_add]
rw [km]
rfl