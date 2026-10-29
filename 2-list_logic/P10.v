Require Export P09.


Theorem material_implication_implies_de_morgan: 
(forall (P Q:Prop), (P -> Q) -> (not P \/ Q)) -> (forall (P Q: Prop), not (not P /\ not Q) -> P \/ Q).
Proof.
  intros H1.
  intros P Q.
  intros H2.
  unfold not in H2.
  assert (HP : ~P \/ P).
  {
    apply (H1 P P).
    intros H. apply H. 
  }
  assert (HQ : ~Q \/ Q).
  {
    apply (H1 Q Q).
    intros H. apply H. 
  }
  destruct HP.
  - destruct HQ.
    + assert (H3 : (P -> False) /\ (Q -> False)). 
    {
      split.
      * apply H.
      * apply H0.
    }
    apply H2 in H3. destruct H3.
    + right. apply H0.
  - left. apply H.
Qed.
