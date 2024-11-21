# Level one

apply h
assumption

# Level two

intro h
assumption

# Level three

intro h
cases h
constructor
assumption
assumption

# Level four

intro
apply h2
apply h1
assumption

# Level five

intro
apply h5
apply h3
apply h1
assumption

# Level six

intro
intro
apply h
constructor
repeat assumption

# Level seven

intro
apply h
apply a.left
apply a.right

# Level eight

intro
cases h
constructor
apply left a
apply right a

# Level nine

repeat {intro; assumption}
intro
constructor
intro
assumption
intro
assumption