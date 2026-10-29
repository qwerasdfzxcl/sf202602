Require Import P05.

Check nth_error_split :
  forall (A : Type) (xs : list A) (n : nat) (x : A),
    nth_error xs n = Some x ->
    exists left right,
      xs = left ++ x :: right /\ length left = n.
