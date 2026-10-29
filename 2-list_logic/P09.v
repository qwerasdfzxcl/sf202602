Require Export P08.

Lemma split_last : forall {A : Type} (h : A) (t : list A),
  exists ys y, h :: t = ys ++ [y].
Proof.
  intros A h t.
  generalize dependent h.
  induction t as [|h2 t' IHt'].
  - intros h. exists []. exists h. simpl. reflexivity.
  - intros h. specialize IHt' with h2.
    destruct IHt'. destruct H.
    exists (h :: x). exists x0.
    rewrite H. simpl. reflexivity.
Qed.

Lemma trim_head_last A (xs : list A) : 2 <=? length xs = true -> exists x ys y, xs = [x] ++ ys ++ [y].
Proof.
  intros H.
  destruct xs.
  - simpl in H. discriminate H.
  - destruct xs.
    + simpl in H. discriminate H.
    + destruct (split_last x0 xs). destruct H0.
      exists x. exists x1. exists x2.
      rewrite H0. simpl. reflexivity.
Qed.
