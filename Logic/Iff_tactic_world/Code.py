# Level one

constructor
assumption
assumption

# Level two

cases h
constructor
assumption
assumption

# Level three

intro h3
apply h2 at h3
apply h1.mp
assumption

# Level four

intro h3
apply h1.mpr at h3
apply h2 at h3
assumption

# Level five

cases h1
cases h2
constructor
intro h3
constructor
apply and_left
apply mp_1
intro x
apply h3
intro ⟨pqnr,rpnq⟩ r
apply x
constructor
intro p
cases pqnr p
left
assumption
right
intro s
apply h
apply mpr
assumption
intro
intro q
apply rpnq
left
repeat assumption
apply mp
assumption
constructor
apply and_left
apply and_right
apply mp_1
intro x
apply h3
intro ⟨pqnr,rpnq⟩ r
apply x
constructor
intro p
cases pqnr p
left
assumption
right
intro s
apply h
apply mpr
assumption
intro sp
apply rpnq
cases sp
left
apply mpr
assumption
right
assumption
apply mp
assumption
apply modus_tollens
assumption
apply and_right
apply and_right
apply mp_1
intro x
apply h3
intro ⟨pqnr, rpnq⟩ r
apply x
constructor
intro p
cases pqnr p
left
assumption
right
intro
apply h
assumption
intro
apply rpnq
left
assumption
apply mp
assumption
intro ⟨p, q, nr⟩
intro
apply mpr_1
constructor
assumption
constructor
assumption
apply modus_tollens
repeat assumption
intro
intro
assumption

# Level six

intro x y
apply h
apply or_assoc.mp
assumption
apply and_assoc.mp
assumption

# Level seven

constructor
intro h
intro y
constructor
intro z
have h1: P ∧ Q := and_intro z y
rw [h] at h1
apply and_left h1
intro
have h1 :R ∧ Q := and_intro a y
cases h
apply mpr at h1
apply and_left h1
intro qpr
constructor
intro ⟨left,q⟩
constructor
apply qpr at q
rw [q] at left
assumption
assumption
intro rq
cases rq
constructor
apply qpr at right
cases right
apply mpr at left
assumption
assumption



