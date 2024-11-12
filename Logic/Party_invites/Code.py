# Level one

exact todo_list

# Level two

exact and_intro p s

# Level three

have ai := and_intro a i
have ou := and_intro o u
exact and_intro ai ou

# Level four

have p := vm.left
exact p

# Level five

have q:= h.right
exact q

# Level six

have a:= h1.left
have u:= h2.right
exact and_intro a u

# Level seven

have h1:=h.left
have h2 := h1.right
have h3 := h2.left
have h4 := h3.left
have h5 := h4.right
exact h5

# Level eight

have psa := h.left
have c := h.right.right.left.left
have cps := and_intro c psa.left
exact and_intro psa.right cps

"And is right-assoicate"