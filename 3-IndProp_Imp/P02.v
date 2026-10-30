Require Export P01.

Lemma ev_sum : forall n m,
  ev n -> ev m -> ev (n + m).
Proof.
  intros n m E1 E2.
  induction E1.
  - apply E2.
  - simpl. apply ev_SS, IHE1.
Qed.

Theorem double_ev : forall m p,
  ev m -> ev (m * p).
Proof. 
  intros m p E.
  induction p.
  - rewrite <- mult_n_O. apply ev_0.
  - rewrite <- mult_n_Sm. apply ev_sum.
    apply IHp. apply E. 
Qed.
