Require Export P07.


Lemma fold_left_last : forall (A B : Type) (f : B -> A -> B) (z0 : B) (xs : list A) (x0 : A),
    fold_left f (xs ++ [x0]) z0 = f (fold_left f xs z0) x0.
Proof.
  intros A B f z0 xs x0.
  generalize dependent z0.
  induction xs as [|h xs' IHxs'].
  - simpl. reflexivity.
  - intros z0. simpl.
    rewrite IHxs'.
    reflexivity.
Qed.
