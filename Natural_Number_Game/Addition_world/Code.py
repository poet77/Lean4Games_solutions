# Level one

induction n with d hd
rw [add_zero]
rfl
rw [add_succ]
rw [hd]
rfl

# Level two

induction b with d hd
rw [add_zero]
rw [add_zero]
rfl
rw [add_succ]
rw [hd]
rw [add_succ]
rfl

# Level three

induction b with d hd
rw [add_zero]
rw [zero_add]
rfl
rw [succ_add]
rw [add_succ]
rw [hd]
rfl

# Level four

induction c with d hd
rw [add_zero]
rw [add_zero]
rfl
rw [add_succ]
rw [add_succ]
rw [add_succ]
rw [hd]
rfl

# Level five

rw [add_assoc]
rw [add_assoc]
rw [add_comm b c]
rfl



