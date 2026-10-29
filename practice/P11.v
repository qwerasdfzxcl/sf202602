Require Export P10.

(* 11. 배중률을 가정하면 귀류법을 사용할 수 있음을 증명하세요.
   외부 고전논리 라이브러리나 P10의 정리를 사용하지 말고,
   주어진 배중률 가정으로 직접 증명하세요. *)

Theorem excluded_middle_implies_raa :
  (forall P : Prop, P \/ ~P) ->
  forall P : Prop, (~P -> False) -> P.
Proof.
  intros H1 P H2.
  specialize H1 with (P := P).
  destruct H1.
  - apply H.
  - apply H2 in H. destruct H.
Qed.