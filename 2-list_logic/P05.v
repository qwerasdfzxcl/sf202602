Require Export P04.


Lemma firstn_exact : forall A n (xs ys : list A), n = length xs -> firstn n (xs ++ ys) = xs.
Proof.
  intros A n.
  induction n as [|n' IHn'].
  - intros xs ys H. destruct xs.
    + simpl. reflexivity.
    + simpl in H. discriminate H.
  - intros xs ys H. simpl.
    destruct xs.
    + simpl in H. discriminate H.
    + simpl. f_equal. apply IHn'.
      simpl in H. injection H as H1. apply H1.   
Qed.
