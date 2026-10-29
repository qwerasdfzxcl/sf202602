Require Export P09.

(* 10. 고전논리 원리의 동치. 고전논리 라이브러리를 가져오지 마세요. *)

Theorem classical_principles_equivalent :
  (forall P : Prop, ~~P -> P) <->
  (forall P Q : Prop, (P -> Q) -> (~P \/ Q)).
Proof.
  split.
  - intros H1. unfold not in H1.
    intros P Q H2. unfold not.
    assert (P \/ ~P).
    {
      unfold not. apply H1. intros H3.
      assert (~P).
      {
        unfold not. intros H4.
        apply H3. left. apply H4.
      }
      apply H3. right. apply H.
    }
    destruct H.
    + right. apply H2. apply H.
    + left. apply H.
  - intros H1 P.
    assert (~P \/ P).
    {
      apply H1. intros H2. apply H2.
    }
    destruct H.
    + intros H2. unfold not in H, H2.
      apply H2 in H. destruct H.
    + intros H2. apply H.
Qed.
