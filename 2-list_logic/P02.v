Require Export P01.

Lemma app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.  
  intros l.
  induction l as [|n l' IHl'].
  - simpl. reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.

Lemma app_assoc : forall l m n : natlist,
  (l ++ m) ++ n = l ++ m ++ n.
Proof.
  intros l m n.
  induction l as [|h l' IHl'].
  - simpl. reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.

Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros l1 l2.
  induction l1 as [|n l1' IHl1'].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1'. rewrite app_assoc. reflexivity. 
Qed.
