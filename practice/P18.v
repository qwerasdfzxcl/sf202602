Require Export P17.

(* 18. reflect와 증거 조립 / 상
   각 원소에 대한 bool 판정이 P를 반영하면, 리스트 전체에 대한 bool 판정도 AllP를 반영함을 증명하세요. *)

Theorem allb_reflect : forall (A : Type) (P : A -> Prop) (test : A -> bool),
  (forall x, reflect (P x) (test x)) ->
  forall xs, reflect (AllP P xs) (allb test xs).
Proof.
  intros A P test H xs.
  induction xs.
  - simpl. apply RTrue. apply AP_nil.
  - simpl. specialize (H x). destruct (test x).
    + simpl. destruct (allb test xs).
      * inversion H. inversion IHxs.
        apply RTrue. apply AP_cons.
        apply H0. apply H1.
      * apply RFalse. intros E.
        inversion IHxs. inversion E.
        apply H0 in H4. destruct H4.
    + simpl. apply RFalse. intros E.
      inversion E. inversion H.
      apply H4 in H2. destruct H2.
Qed. 
