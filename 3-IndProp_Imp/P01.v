Require Export D.
Export Natord.
Require Export Tactics. 

Theorem ev_sum_not : forall n m, ev (n + m) -> not (ev n) -> not (ev m).
Proof.
  intros n m H1 H2 H3.
  assert (ev n).
  {
    induction H3.
    + rewrite <- plus_n_O in H1. apply H1.
    + repeat rewrite <- plus_n_Sm in H1.
      inversion H1.
      apply IHev, H0.
  }
  apply H2 in H. destruct H.
Qed.
