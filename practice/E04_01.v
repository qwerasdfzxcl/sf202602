Require Import P04.

Check firstn_firstn :
  forall (A : Type) (n m : nat) (xs : list A),
    firstn n (firstn m xs) = firstn (min n m) xs.
