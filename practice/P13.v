Require Export P12.

(* 13. 귀납적 관계와 존재 증거 / 상
   귀납적 부등식과 두 수의 차이를 나타내는 존재 명제가 동치임을 증명하세요. 표준 Nat.le로 바꾸지 말고 rle의 생성자를 사용하세요. *)

Theorem rle_gap : forall n m,
  rle n m <-> exists d, m = n + d.
Proof.
  intros n m. split.
  - intros E. induction E.
    + exists 0. rewrite <- plus_n_O. reflexivity.
    + destruct IHE. exists (S x).
      rewrite <- plus_n_Sm.
      f_equal. apply H.
  - intros []. 
    generalize dependent m.
    induction x.
    + intros m H. rewrite <- plus_n_O in H. rewrite H. apply rle_n.
    + intros m H. rewrite H. rewrite <- plus_n_Sm. apply rle_S.
      apply IHx. reflexivity.
Qed.
