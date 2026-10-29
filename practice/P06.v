Require Export P05.

(* 06. 모든 위치의 값이 같으면 리스트도 같습니다. 길이 가정은 없습니다. *)

Theorem nth_error_ext :
  forall (A : Type) (xs ys : list A),
    (forall n, nth_error xs n = nth_error ys n) -> xs = ys.
Proof.
  intros A xs.
  induction xs as [|x xs' IHxs'].
  - intros ys H. specialize H with (n := 0) as H0.
    simpl in H0. destruct ys.
    + reflexivity.
    + simpl in H0. discriminate H0.
  - intros ys H. specialize H with (n := 0) as H0.
    destruct ys as [|y ys'].
    + simpl in H0. discriminate H0.
    + simpl in H0. injection H0 as H0.
      rewrite H0. f_equal.
      apply IHxs'.
      intros n. apply (H (S n)).
Qed.