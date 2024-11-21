# Level one

use 0
rw [add_zero]
rfl

# Level two

use x
rw [zero_add]
rfl

# Level three

use 1
decide

# Level four

cases hxy with a ha
cases hyz with b hb
use a + b
rw [ha] at hb
rw [add_assoc] at hb
exact hb

# Level five

cases hx with a ha
symm at ha
apply add_right_eq_zero at ha
exact ha

# Level six

cases hxy with a ha
cases hyx with b hb
rw [ha] at hb
symm at hb
rw [add_assoc] at hb
apply add_right_eq_self at hb
apply add_right_eq_zero at hb
rw [hb] at ha
rw [add_zero] at ha
symm at ha
exact ha

# Level seven

cases h with hx hy
right
exact hx

left
exact hy

# Level eight

induction y with d hd
right
apply zero_le
cases hd with h1 h2
left
cases d with b
apply le_zero at h1
rw [h1]
apply le_succ_self
apply le_trans x (succ b) (succ (succ b))
exact h1
apply le_succ_self (succ b)
cases h2 with e he
cases e with a
rw [he]
left
rw [add_zero]
use 1
exact succ_eq_add_one d
right
use a
rw [add_succ] at he
rw [succ_add]
apply he

# Level nine

cases hx with d hd
use d
rw [succ_add] at hd
apply succ_inj at hd
apply hd

# Level ten

cases x with d
left
rfl
rw [one_eq_succ_zero] at hx
apply succ_le_succ at hx
apply le_zero at hx
rw [hx]
right
apply one_eq_succ_zero


# Level eleven

cases x with y
left
rfl
cases y with z
right
left
rw [one_eq_succ_zero]
rfl
rw [two_eq_succ_one, one_eq_succ_zero] at hx ⊢
apply succ_le_succ at hx
apply succ_le_succ at hx
apply le_zero at hx
rw [hx]
right
right
rfl
