Require Export P13.

(* 14. 두 개의 관계 증거 / 상
   subseq xs ys는 xs가 ys에서 일부 원소를 순서대로 골라 얻는 부분수열이라는 뜻입니다. 그 관계의 추이성을 증명하세요. *)

Theorem subseq_trans : forall (A : Type) (xs ys zs : list A),
  subseq xs ys -> subseq ys zs -> subseq xs zs.
Proof.
  intros A xs ys zs E1 E2.
  generalize dependent xs.
  induction E2.
  - intros xs E1. inversion E1. apply sub_nil.
  - intros xs' E1. destruct xs'.
    + apply sub_nil.
    + inversion E1.
      * apply sub_keep, IHE2, H0.
      * apply sub_skip, IHE2, H1.
  - intros xs' E1. apply sub_skip, IHE2, E1.
Qed.
