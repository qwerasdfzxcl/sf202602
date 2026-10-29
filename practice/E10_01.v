Require Import P10.

Check classical_principles_equivalent :
  (forall P : Prop, ~~P -> P) <->
  (forall P Q : Prop, (P -> Q) -> (~P \/ Q)).
