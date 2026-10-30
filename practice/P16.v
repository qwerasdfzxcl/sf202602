Require Export P15.

(* 16. 정규식 증거 귀납법 / 상
   같은 정규식의 Star에 매칭되는 두 리스트를 이어 붙여도 그 Star에 매칭됨을 증명하세요. 복잡한 인덱스를 귀납할 때 원래 형태를 보존하는 방법을 생각해보세요. *)

Theorem star_concat : forall (A : Type) (s1 s2 : list A) (re : reg_exp A),
  s1 =~ Star re -> s2 =~ Star re -> (s1 ++ s2) =~ Star re.
Proof.
  intros A s1 s2 re E1 E2.
  remember (Star re) as r eqn : E.
  generalize dependent s2.
  generalize dependent re.
  induction E1.
  - intros re H. discriminate H.
  - intros re H. discriminate H.
  - intros re H. discriminate H. 
  - intros re H. discriminate H. 
  - intros re H. discriminate H.
  - intros re H s2 E. simpl. apply E.
  - intros re H s0 E.
    specialize (IHE1_2 re H s0 E).
    rewrite app_assoc.
    apply (MStarApp s1 (s2 ++ s0) r E1_1 IHE1_2).
Qed.
    
