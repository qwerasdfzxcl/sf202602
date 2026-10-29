Require Export P03.


Theorem rev_involutive : forall l : natlist,
  rev ((rev l)) = l.
Proof.
  intros l.
  induction l as [|n l' IHl'].
  - simpl. reflexivity.
  - simpl. rewrite distr_rev.
    rewrite IHl'.
    simpl. reflexivity. 
Qed.
