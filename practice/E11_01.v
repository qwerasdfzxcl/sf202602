Require Import P11.

Check excluded_middle_implies_raa :
  (forall P : Prop, P \/ ~P) ->
  forall P : Prop, (~P -> False) -> P.
