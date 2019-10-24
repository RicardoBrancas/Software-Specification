sig A { r: B}
sig B {}

pred p1 [] {all x, x' : A, y : B | x->y in r and x'->y in r implies x=x'}
pred p2 [] {all x: A | lone x.r}
pred p3 [] {no ~r.r - iden}
pred p4 [] {r in A -> one B}

assert p12 { p1 <=> p2 }
assert p13 { p1 <=> p3 }
assert p14 { p1 <=> p4 }
assert p23 { p2 <=> p3 }
assert p24 { p2 <=> p4 }
assert p34 { p3 <=> p4 }

check p12
check p13
check p14
check p23
check p24
check p34
