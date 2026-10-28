Require Export P03.

Theorem xorb_eq_andb :
  forall (b c : bool),
  (xorb b c = andb b c) ->
  b = c.
Proof.
  intros b c.
  intros H.
  destruct b, c.
  - simpl. reflexivity.
  - simpl in H. simpl. rewrite H. reflexivity.
  - simpl in H. simpl. rewrite H. reflexivity.
  - simpl. reflexivity.
Qed.
