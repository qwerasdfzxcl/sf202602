Require Export P05.
Export Imp.

Lemma nat_div_1 : forall n m,
  Nat.divmod n 0 m 0 = (n + m, 0).
Proof.
  intros n.
  induction n.
  - intros m. simpl. reflexivity.
  - intros m. simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem optimize_1div_sound: forall a,
  aeval (optimize_1div a) = aeval a.
Proof. 
  intros a.
  induction a.
  - simpl. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - destruct a2.
    + destruct n.
      * simpl. rewrite IHa1. reflexivity.
      * destruct n.
        --simpl. unfold o_bind. unfold o_map. unfold o_join. simpl.
          destruct (aeval a1).
          ++rewrite nat_div_1. simpl. rewrite <- plus_n_O. reflexivity.
          ++reflexivity.
        --simpl. rewrite IHa1. reflexivity.
    + simpl. rewrite IHa1. simpl in IHa2. rewrite IHa2. reflexivity.
    + simpl. rewrite IHa1. simpl in IHa2. rewrite IHa2. reflexivity.
    + simpl. rewrite IHa1. simpl in IHa2. rewrite IHa2. reflexivity.
    + simpl. rewrite IHa1. simpl in IHa2. rewrite IHa2. reflexivity.
Qed.
