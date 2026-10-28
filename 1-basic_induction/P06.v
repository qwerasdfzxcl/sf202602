Require Export P05.

Lemma plus_0_r : forall n : nat,
  n + 0 = n.
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Lemma plus_succ_n : forall n m : nat,
  n + S m = S (n + m).
Proof.
  intros n m. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed. 

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [|n' IHn'].
  - simpl. rewrite plus_0_r. reflexivity.
  - simpl. rewrite IHn'. rewrite plus_succ_n. reflexivity.
Qed.



