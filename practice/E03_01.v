Require Import P03.

Check map_rev :
  forall (A B : Type) (f : A -> B) (xs : list A),
    map f (rev xs) = rev (map f xs).
