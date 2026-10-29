Require Export P05.

Lemma removelast_l_x : forall (l : natlist) (x : nat),
  removelast (l ++ [x]) = l.
Proof.
  intros l x.
  induction l as [|h l' IHl'].
  - simpl. reflexivity.
  - destruct l'.
    + simpl. reflexivity.
    + replace (removelast ((h :: x0 :: l') ++ [x])) 
      with (h :: removelast ((x0 :: l') ++ [x])).
      * rewrite IHl'. reflexivity.
      * simpl. reflexivity.
Qed.

Theorem rev_removelast_rev_tl : forall l : natlist,
  rev (removelast (rev l)) = tl l.
Proof.
  intros l.
  destruct l.
  - simpl. reflexivity.
  - simpl. rewrite removelast_l_x.
    rewrite rev_involutive.
    reflexivity.
Qed.
