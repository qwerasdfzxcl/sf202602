Require Export P07.

(* 08. 함수의 단사성과 map의 단사성이 동치임을 증명하세요. *)

Theorem map_injective_iff :
  forall (A B : Type) (f : A -> B),
    (forall x y, f x = f y -> x = y) <->
    (forall xs ys : list A,
       map f xs = map f ys -> xs = ys).
Proof.
  intros A B f. split.
  - intros H1 xs.
    induction xs as [|x xs' IHxs'].
    + intros ys H2. destruct ys.
      * reflexivity.
      * simpl in H2. discriminate H2.
    + intros ys H2. destruct ys as [|y ys'].
      * simpl in H2. discriminate H2.
      * simpl in H2.
        injection H2 as H3 H4.
        apply H1 in H3. rewrite H3. f_equal.
        apply IHxs'. apply H4.
  - intros H1 x y H2.
    specialize H1 with (xs := [x]) (ys := [y]).
    simpl in H1.
    assert ([x] = [y]).
    {
      apply H1. rewrite H2. reflexivity.
    } 
    injection H as H. apply H.
Qed.
    

