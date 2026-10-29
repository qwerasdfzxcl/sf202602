Require Export P02.

(* 03. 두 재귀 함수의 상호작용. *)

Lemma map_app_f_x : forall (A B : Type) (f : A -> B) (l : list A) (x : A),
  map f (l ++ [x]) = map f l ++ [f x].
Proof.
  intros A B f l x.
  induction l as [|h l' IHl'].
  - simpl. reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.

Theorem map_rev :
  forall (A B : Type) (f : A -> B) (xs : list A),
    map f (rev xs) = rev (map f xs).
Proof.
  intros A B f xs.
  induction xs as [|x xs' IHxs'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHxs'.
    rewrite map_app_f_x.
    reflexivity.
Qed.
