Require Export P04.

Print evenb.

Lemma xor_comm : forall (a b : bool),
  xorb a b = xorb b a.
Proof.
  intros a b.
  destruct a, b.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma evenb_S : forall n, xorb (evenb (S n)) (evenb n) = true.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - replace (evenb (S (S n'))) with (evenb n').
    + rewrite xor_comm. rewrite IHn'. reflexivity. 
    + simpl. reflexivity.
Qed.