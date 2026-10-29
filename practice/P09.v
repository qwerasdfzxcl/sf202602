Require Export P08.

(* 09. 배중률 없이 증명하는 이중부정과 드모르간 법칙. *)

Theorem double_neg_or :
  forall P Q : Prop,
    ~~(P \/ Q) <-> ~(~P /\ ~Q).
Proof.
  intros P Q. split.
  - intros H1. unfold not in H1.
    unfold not. intros H2. destruct H2 as [H2 H3].
    apply H1. intros H4. destruct H4.
    + apply H2. apply H.
    + apply H3. apply H.
  - intros H1. unfold not in H1.
    unfold not. intros H2.
    apply H1. split.
    + intros H3. apply H2. left. apply H3.
    + intros H3. apply H2. right. apply H3.
Qed.
