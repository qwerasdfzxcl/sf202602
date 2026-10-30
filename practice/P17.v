Require Export P16.

(* 17. 정규식과 이전 정리의 재사용 / 최상
   Star를 두 번 씌워도 매칭되는 리스트의 범위가 변하지 않음을 증명하세요. *)

Lemma app_nil_r : forall (A : Type) (s : list A),
  s ++ [] = s.
Proof.
  intros A s.
  induction s.
  - reflexivity.
  - simpl. rewrite IHs. reflexivity.
Qed. 

Theorem star_flatten : forall (A : Type) (s : list A) (re : reg_exp A),
  s =~ Star (Star re) <-> s =~ Star re.
Proof.
  intros A s re. split.
  - intros E1.
    remember (Star (Star re)) as t.
    generalize dependent re.
    induction E1.
    + intros re H. discriminate H.
    + intros re H. discriminate H.
    + intros re H. discriminate H.
    + intros re H. discriminate H.
    + intros re H. discriminate H.
    + intros re H. apply MStar0.
    + intros re H.
      specialize (IHE1_2 re H).
      injection H as H. rewrite H in E1_1.
      apply star_concat. apply E1_1. apply IHE1_2.
  - intros E.
    rewrite <- (app_nil_r A s).
    apply MStarApp. apply E. apply MStar0.
Qed.
        
