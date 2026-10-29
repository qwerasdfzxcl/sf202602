Require Import P08.

Check map_injective_iff :
  forall (A B : Type) (f : A -> B),
    (forall x y, f x = f y -> x = y) <->
    (forall xs ys : list A,
       map f xs = map f ys -> xs = ys).
