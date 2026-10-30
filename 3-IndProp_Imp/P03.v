Require Export P02.

Lemma le_trans : forall m n o,
  m <= n -> n <= o -> m <= o.
Proof.
  intros m n o E1 E2.
  induction E2.
  apply E1.
  apply le_S, IHE2, E1.
Qed.

Lemma le_plus : forall a b,
  a <= a + b.
Proof.
  intros a b.
  induction b.
  - rewrite <- plus_n_O. apply le_n.
  - rewrite <- plus_n_Sm. apply le_S, IHb.
Qed. 
  
Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  intros n1 n2 m E.
  unfold lt in E.
  split.
  - apply le_trans with (S (n1 + n2)).
    + apply (le_plus (S n1) n2).
    + apply E.
  - apply le_trans with (S (n1 + n2)).
    + rewrite Nat.add_comm.
      apply (le_plus (S n2) n1).
    + apply E.
Qed.
