Require Import P18.

Check allb_reflect : forall (A : Type) (P : A -> Prop) (test : A -> bool),
  (forall x, reflect (P x) (test x)) ->
  forall xs, reflect (AllP P xs) (allb test xs).
