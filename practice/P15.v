Require Export P14.

(* 15. 관계의 역분석과 리스트 분해 / 상
   연결된 리스트의 부분수열을 앞쪽에서 고른 부분과 뒤쪽에서 고른 부분으로 분해하세요. *)

Theorem subseq_app_split : forall (A : Type) (xs ys zs : list A),
  subseq xs (ys ++ zs) ->
  exists left right,
    xs = left ++ right /\ subseq left ys /\ subseq right zs.
Proof.
  intros A xs ys.
  generalize dependent xs.
  induction ys.
  - intros xs zs E. exists [], xs.
    split. reflexivity.
    split. apply sub_nil.
    apply E.
  - intros xs zs E. inversion E.
    + exists [], [].
      split. reflexivity.
      split. apply sub_nil.
      apply sub_nil.
    + specialize IHys with xs0 zs. apply IHys in H1.
      destruct H1 as [L [R H1]].
      destruct H1 as [HA [HB HC]].
      exists (x :: L), R.
      split. simpl. f_equal. apply HA.
      split. apply sub_keep, HB.
      apply HC.
    + specialize IHys with xs zs. apply IHys in H1.
      destruct H1 as [L [R H1]].
      destruct H1 as [HA [HB HC]].
      exists L, R.
      split. apply HA. split. apply sub_skip, HB. apply HC.
Qed.

    