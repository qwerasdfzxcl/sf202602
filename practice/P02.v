Require Export P01.

(* 02. 리스트 연결의 소거: 길이나 rev를 이용하지 않고 풀어보세요. *)

Theorem app_cancel_left :
  forall (A : Type) (prefix xs ys : list A),
    prefix ++ xs = prefix ++ ys -> xs = ys.
Proof.
  intros A prefix xs ys H.
  induction prefix as [|h t IHt].
  - simpl in H. apply H.
  - simpl in H. injection H as H.
    apply IHt. apply H.
Qed.
