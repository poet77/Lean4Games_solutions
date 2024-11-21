# Level one

rw [pow_zero]
rfl

# Level two

rw [pow_succ]
rw [mul_zero]
rfl

# Level three

rw [one_eq_succ_zero]
rw [pow_succ]
rw [pow_zero]
rw [one_mul]
rfl

# Level four

induction m with k km
rw [pow_zero]
rfl

rw [pow_succ]
rw [mul_one]
exact km

# Level five

rw [two_eq_succ_one]
rw [pow_succ]
rw [pow_one]
rfl

# Level six

induction n with k kn
rw [add_zero]
rw [pow_zero]
rw [mul_one]
rfl

rw [pow_succ]
rw [add_succ]
rw [pow_succ]
rw [kn]
rw [mul_assoc]
rfl

# Level seven

induction n with l nl
rw [pow_zero]
rw [pow_zero]
rw [pow_zero]
rw [mul_one]
rfl
rw [pow_succ]
rw [pow_succ]
rw [nl]
rw [mul_comm a b]
rw [← mul_assoc]
rw [mul_comm]
rw [mul_assoc]
rw [← mul_assoc]
rw [mul_comm a (a ^ l)]
rw [pow_succ]
rfl

# Level eight

induction n with t nt
rw [pow_zero]
rw [mul_zero]
rw [pow_zero]
rfl
rw [succ_eq_add_one]
rw [pow_add]
rw [mul_add]
rw [pow_add]
rw [nt]
rw [pow_one]
rw [mul_one]
rfl

# Level nine

rw [two_eq_succ_one]
rw [pow_succ]
rw [pow_one]
rw [mul_add]
rw [add_mul]
rw [add_mul]
rw [mul_comm b a]
repeat rw [pow_succ]
rw [succ_mul]
rw [add_mul]
rw [one_mul]
repeat rw [pow_one]
rw [add_comm (a*b) (b*b)]
rw [add_right_comm]
rw [← add_assoc]
rw [← add_assoc]
rfl

# Level ten

# TOO HARD...