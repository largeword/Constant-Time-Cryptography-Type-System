TODO:

- substitution : typevar -> Type
- handle application of (a^L -> a^L)^H is H

- constraints in array, list pair
- Subtyping for case list, other parts??

- Parsing Changes example

-- empty case:
   <|> try (char '^' *> pSuperscript)
   <|> return (LabelVar (AnnotationVar ...))

1 :: Nat^b0
fn x -> x :: (a0^L -> a0^L)^L

a_i -> a_(-i-1)

(1, 1, 1) :: (Nat^b0, Nat^b1, Nat)

(Nat^b0, Nat^b1, Nat^b-1)^b-2

start ParserState = -1
ParserState = -3

-i + state
(Nat^b-3, Nat^b-4, Nat^b-1)^b-2


notes:
L <= L
L <= H
H <= H

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
