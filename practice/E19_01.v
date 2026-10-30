Require Import P19.

Check filterb_subseq : forall (A : Type) (test : A -> bool) (xs : list A),
  subseq (filterb test xs) xs.

Check filterb_spec : forall (A : Type) (P : A -> Prop) (test : A -> bool),
  (forall x, reflect (P x) (test x)) ->
  forall (xs : list A) x,
    In x (filterb test xs) <-> In x xs /\ P x.
