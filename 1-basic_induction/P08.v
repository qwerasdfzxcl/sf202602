Require Export P07.

Lemma plus_assoc : forall n m p : nat,
  n + m + p = n + (m + p).
Proof.
  intros n m p. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed. 

Theorem mult_plus_distr_l : forall n m p : nat,
  p * (n + m)= (p * n) + (p * m).
Proof.
  intros n m p. induction p as [|p' IHp'].
  - simpl. reflexivity.
  - simpl. rewrite IHp'. 
    rewrite plus_assoc.
    rewrite <- (plus_assoc m (p' * n) (p' * m)).
    rewrite (plus_comm m (p' * n)).
    repeat rewrite <- plus_assoc.
    reflexivity.
Qed.
