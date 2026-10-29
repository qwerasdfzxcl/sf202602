Require Export P06.

(* 07. 누적값이 바뀌는 재귀. 두 정리를 모두 증명하세요. *)

Theorem fold_left_app :
  forall (A B : Type) (f : B -> A -> B)
         (xs ys : list A) (z : B),
    fold_left f (xs ++ ys) z =
    fold_left f ys (fold_left f xs z).
Proof.
  intros A B f xs.
  induction xs as [|x xs' IHxs'].
  - intros ys z. simpl. reflexivity.
  - intros ys z. simpl.
    specialize IHxs' with (ys := ys) (z := f z x).
    rewrite IHxs'. reflexivity.
Qed. 

Lemma app_assoc : forall (A : Type) (a b c : list A),
  (a ++ b) ++ c = a ++ b ++ c.
Proof.
  intros A a b c.
  induction a as [|x a' IHa'].
  - simpl. reflexivity.
  - simpl. rewrite IHa'. reflexivity.
Qed.


Theorem fold_left_rev_acc :
  forall (A : Type) (xs acc : list A),
    fold_left (fun acc x => x :: acc) xs acc = rev xs ++ acc.
Proof.
  intros A xs.
  induction xs as [|x xs' IHxs'].
  - intros acc. simpl. reflexivity.
  - intros acc. simpl.
    specialize IHxs' with (acc := x :: acc).
    rewrite IHxs'.
    rewrite app_assoc.
    simpl. reflexivity.
Qed.
