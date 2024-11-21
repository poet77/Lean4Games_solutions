# Level one

cases h with d hd
use d * t
rw [hd]
rw [add_mul]
rfl

# Level two

intro hb
apply h
rw [hb, mul_zero]
rfl

# Level three

cases a with d
tauto
use d
rfl

# Level four

apply eq_succ_of_ne_zero at ha
cases ha with n hn
use n
rw [hn, succ_eq_add_one, add_comm]
rfl

# Level five

apply mul_left_ne_zero at h
apply one_le_of_ne_zero at h
apply mul_le_mul_right 1 b a at h
rw [one_mul] at h
rw [mul_comm] at h
exact h

# Level six

have h2 : x * y ≠ 0
rw [h]
exact one_ne_zero
apply le_mul_right at h2
rw [h] at h2
apply le_one at h2
cases h2 with h0 h1
rw [h0, zero_mul] at h
tauto
exact h1

# Level seven

apply eq_succ_of_ne_zero at ha
apply eq_succ_of_ne_zero at hb
cases ha with c hc
cases hb with d hd
rw [hc, hd]
rw [mul_succ]
rw [add_succ]
symm
apply zero_ne_succ

# Level eight

have h2 := mul_ne_zero a b
tauto

# Level nine

induction b with d hd generalizing c
rw [mul_zero] at h
symm at h
apply mul_eq_zero at h
cases h with h1 h2
tauto
symm
exact h2
cases c with e
rw [mul_succ, mul_zero] at h
apply add_left_eq_zero at h
tauto
rw [mul_succ, mul_succ] at h
apply add_right_cancel at h
apply hd at h
rw [h]
rfl

# Level ten

nth_rewrite 2 [← mul_one a] at h
exact mul_left_cancel a b 1 ha h