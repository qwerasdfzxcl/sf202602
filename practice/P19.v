Require Export P18.

(* 19. 종합: 리스트, 관계, reflect / 상
   두 정리를 모두 증명하세요. 두 번째 정리에서 bool 판정과 P를 연결하는 데에는 주어진 reflect 가정만 사용하세요. *)

Theorem filterb_subseq : forall (A : Type) (test : A -> bool) (xs : list A),
  subseq (filterb test xs) xs.
Proof.
  intros A test xs.
  induction xs.
  - simpl. apply sub_nil.
  - simpl. destruct (test x).
    + apply sub_keep, IHxs.
    + apply sub_skip, IHxs.
Qed. 

Theorem filterb_spec : forall (A : Type) (P : A -> Prop) (test : A -> bool),
  (forall x, reflect (P x) (test x)) ->
  forall (xs : list A) x,
    In x (filterb test xs) <-> In x xs /\ P x.
Proof.
  intros A P test H1 xs x. split.
  - intros H2. induction xs.
    + simpl in H2. destruct H2.
    + simpl in H2. destruct (test x0) eqn : E.
      * simpl in H2. destruct H2.
        split. simpl. left. apply H.
        specialize (H1 x).
        rewrite H in E.
        inversion H1. apply H2. rewrite E in H0. discriminate H0.
        apply IHxs in H. simpl. destruct H.
        split. right. apply H. apply H0.
      * apply IHxs in H2. simpl. destruct H2.
        split. right. apply H. apply H0.
  - intros [H2 H3]. induction xs.
    + simpl in H2. destruct H2.
    + simpl in H2. destruct H2.
      * specialize (H1 x). 
        inversion H1. rewrite H. simpl. 
        rewrite <- H0. simpl. left. reflexivity.
        apply H2 in H3. destruct H3.
      * apply IHxs in H. simpl. destruct (test x0).
        simpl. right. apply H. apply H.
Qed.
