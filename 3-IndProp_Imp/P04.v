Require Export P03.
Export Regexp.

Lemma fold_left_app : forall (T : Type) (ss : list (list T)) (a : list T),
  fold_left (app (A:=T)) ss a = a ++ fold_left (app (A:=T)) ss [].
Proof.
  intros T ss.
  induction ss.
  - intros a. simpl. rewrite app_nil_r. reflexivity.
  - intros b. simpl. rewrite IHss.
    rewrite <- app_assoc.
    f_equal.
    rewrite <- IHss. reflexivity.
Qed.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold_left (app (A := _)) ss [] =~ Star re.
Proof.
  intros T ss re H.
  induction ss.
  - simpl. apply MStar0.
  - simpl. rewrite fold_left_app.
    apply MStarApp.
    + apply H. simpl. left. reflexivity.
    + apply IHss. intros s H2. apply H.
      simpl. right. apply H2.
Qed.
