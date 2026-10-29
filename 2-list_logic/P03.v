Require Export P02.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
  intros n X.
  induction n as [|n' IHn'].
  - intros l H. destruct l.
    + simpl. reflexivity.
    + simpl in H. discriminate H.
  - intros l H. destruct l.
    + simpl. reflexivity.
    + simpl. apply IHn'.
      simpl in H.
      injection H as H1.
      apply H1.
Qed.
