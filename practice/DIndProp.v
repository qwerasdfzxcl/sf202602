Require Export P11.
From Coq Require Export Arith.PeanoNat.

(* 기존 D.v의 list, option, app, map 등을 사용합니다.
   아래 정의의 성질은 필요한 만큼 보조 정리로 직접 증명하세요. *)
Module IP.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS (n : nat) : ev n -> ev (S (S n)).

Inductive rle (n : nat) : nat -> Prop :=
| rle_n : rle n n
| rle_S (m : nat) : rle n m -> rle n (S m).

Inductive subseq {A : Type} : list A -> list A -> Prop :=
| sub_nil (ys : list A) : subseq [] ys
| sub_keep (x : A) (xs ys : list A) :
    subseq xs ys -> subseq (x :: xs) (x :: ys)
| sub_skip (x : A) (xs ys : list A) :
    subseq xs ys -> subseq xs (x :: ys).

Inductive reg_exp (A : Type) : Type :=
| EmptySet
| EmptyStr
| Char (x : A)
| App (r1 r2 : reg_exp A)
| Union (r1 r2 : reg_exp A)
| Star (r : reg_exp A).

Arguments EmptySet {A}.
Arguments EmptyStr {A}.
Arguments Char {A} _.
Arguments App {A} _ _.
Arguments Union {A} _ _.
Arguments Star {A} _.

Reserved Notation "s '=~' re" (at level 80).
Inductive exp_match {A : Type} : list A -> reg_exp A -> Prop :=
| MEmpty : [] =~ EmptyStr
| MChar (x : A) : [x] =~ Char x
| MApp s1 r1 s2 r2 :
    s1 =~ r1 -> s2 =~ r2 -> (s1 ++ s2) =~ App r1 r2
| MUnionL s r1 r2 : s =~ r1 -> s =~ Union r1 r2
| MUnionR s r1 r2 : s =~ r2 -> s =~ Union r1 r2
| MStar0 r : [] =~ Star r
| MStarApp s1 s2 r :
    s1 =~ r -> s2 =~ Star r -> (s1 ++ s2) =~ Star r
where "s '=~' re" := (exp_match s re).

Inductive reflect (P : Prop) : bool -> Prop :=
| RTrue : P -> reflect P true
| RFalse : ~P -> reflect P false.

Inductive AllP {A : Type} (P : A -> Prop) : list A -> Prop :=
| AP_nil : AllP P []
| AP_cons x xs : P x -> AllP P xs -> AllP P (x :: xs).

Fixpoint allb {A : Type} (test : A -> bool) (xs : list A) : bool :=
  match xs with
  | [] => true
  | x :: xs' => andb (test x) (allb test xs')
  end.

Fixpoint filterb {A : Type} (test : A -> bool) (xs : list A) : list A :=
  match xs with
  | [] => []
  | x :: xs' => if test x then x :: filterb test xs' else filterb test xs'
  end.

End IP.
Export IP.
