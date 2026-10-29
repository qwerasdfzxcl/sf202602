Require Import P02.

Check app_cancel_left :
  forall (A : Type) (prefix xs ys : list A),
    prefix ++ xs = prefix ++ ys -> xs = ys.
