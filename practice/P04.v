Require Export P03.

(* 04. firstn 두 번 적용하기. min은 두 자연수 중 작은 값입니다. *)

Theorem firstn_firstn :
  forall (A : Type) (n m : nat) (xs : list A),
    firstn n (firstn m xs) = firstn (min n m) xs.
Proof.
  intros A n m xs.
  generalize dependent m.
  generalize dependent n.
  induction xs as [|x xs' IHxs'].
  - intros n m. destruct n, m.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - intros n m. destruct n, m.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. f_equal. apply IHxs'.
Qed.