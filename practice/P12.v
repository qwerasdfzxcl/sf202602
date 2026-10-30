Require Export DIndProp.

(* 12. 증거 귀납법 / 중상
   ev n이라는 증거를 활용하여 덧셈의 짝수 성질을 양방향으로 증명하세요. *)

Theorem ev_add_cancel : forall n m,
  ev n -> (ev (n + m) <-> ev m).
Proof.
  intros n m H1.
  split.
  - intros H2.
    induction H1.
    + apply H2.
    + simpl in H2. inversion H2. apply IHev, H0.
  - intros H2.
    induction H1.
    + apply H2.
    + simpl. apply ev_SS, IHev.
Qed.
