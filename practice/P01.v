Require Export D.

(* 01. 산술과 귀납법: 같은 수를 두 번 더한 결과가 같으면 원래 수도 같다. *)

Lemma add_succ_r : forall n m : nat,
  n + S m = S (n + m).
Proof.
  intros n m.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed. 

Theorem double_injective :
  forall n m : nat,
    n + n = m + m -> n = m.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - intros m H. simpl. destruct m.
    + reflexivity.
    + simpl in H. discriminate H.
  - intros m H. destruct m.
    + simpl in H. discriminate H.
    + simpl in H. injection H as H.
      repeat rewrite add_succ_r in H.
      injection H as H.
      apply IHn' in H.
      f_equal. apply H.
Qed.
