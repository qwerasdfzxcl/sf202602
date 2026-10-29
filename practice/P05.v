Require Export P04.

(* 05. 인덱스로 리스트 분해하기. 앞부분의 길이까지 증명하세요. *)

Theorem nth_error_split :
  forall (A : Type) (xs : list A) (n : nat) (x : A),
    nth_error xs n = Some x ->
    exists left right,
      xs = left ++ x :: right /\ length left = n.
Proof.
  intros A xs n x H.
  generalize dependent n.
  induction xs as [|h xs' IHxs'].
  - intros n H. destruct n.
    + simpl in H. discriminate H.
    + simpl in H. discriminate H.
  - intros n H. destruct n.
    + simpl in H. injection H as H.
      exists []. exists xs'. split.
      * simpl. rewrite H. reflexivity.
      * simpl. reflexivity.
    + simpl in H. apply IHxs' in H.
      destruct H as [left [right H]].
      destruct H as [H1 H2].
      exists (h :: left). exists right. split.
      * rewrite H1. simpl. reflexivity.
      * simpl. f_equal. apply H2.
Qed.   
