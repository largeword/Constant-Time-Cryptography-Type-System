TODO:
- Constraint datatype
- W should return Constraint
- Subtyping
- Label rules for simple things: Nat, Bool
- Label rules & CTC rule in if, arrays, etc, return error if violated
- Constraints solver

notes:
H <= L


let div5 = fn x -> x / 5 -- div5 L -> L

/ is not constant --> e1 / e2 , e1 : L, e2 : L

if ec then e1 else e2
-- ec must be L
e1 e2 can subtype

ea[ei] = e
ea[ei]

1 L

true L

1 :: Nat^H

(1 :: Nat^H) :: Nat^L -- error!

ei must be L

t ea = t e
ea : H, e : L

(l1, l2) -> subtype of l1 & l2

array l -> l

List l -> l

case e of (x, y) -->


case e_list of e_list L
  [] -> ... t1
  x:xs -> t2
