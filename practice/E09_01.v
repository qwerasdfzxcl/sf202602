Require Import P09.

Check double_neg_or :
  forall P Q : Prop,
    ~~(P \/ Q) <-> ~(~P /\ ~Q).
